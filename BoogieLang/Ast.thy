section \<open>Semantics of the AST\<close>

theory Ast
  imports Main Semantics Lang BackedgeElim

begin

subsection \<open>AST definition\<close>

type_synonym name = string
type_synonym label = string
type_synonym guard = expr
type_synonym invariant = expr

datatype transfer_cmd
 = Goto label
 | Return

datatype parsed_structured_cmd
 = ParsedIf "guard option" "bigblock list" "bigblock list"
 | ParsedWhile "guard option" "invariant list" "bigblock list"
 | ParsedBreak nat
 | WhileWrapper parsed_structured_cmd

and bigblock 
 = BigBlock "name option" "cmd list" "parsed_structured_cmd option" "transfer_cmd option"


text \<open>A Boogie statement represented as an AST is a list of \<^typ>\<open>bigblock\<close>\<close>

type_synonym ast = "bigblock list"

subsection \<open>AST semantics\<close>

text \<open>We define a continuation-based small-step semantics.\<close>

datatype cont 
 = KStop 
 | KSeq "bigblock" cont
 | KEndBlock cont 

type_synonym ('a, 'm) ast_config = "bigblock * cont * (('a, 'm) state)"

fun convert_list_to_cont :: "bigblock list \<Rightarrow> cont \<Rightarrow> cont" where
    "convert_list_to_cont [] cont0 = cont0"
  | "convert_list_to_cont (x#xs) cont0 = KSeq x (convert_list_to_cont xs cont0)"

text\<open>auxillary function to find the label a Goto statement is referring to\<close>
fun find_label :: "label \<Rightarrow> bigblock list \<Rightarrow> cont \<Rightarrow> ((bigblock * cont) option)" where
    "find_label lbl [] cont = None" 
  | "find_label lbl ((BigBlock bb_name cmds None None) # []) cont = 
      (if (Some lbl = bb_name) then (Some ((BigBlock bb_name cmds None None), cont)) else (None))" 
  | "find_label lbl ((BigBlock bb_name cmds None None) # bbs) cont = 
      (if (Some lbl = bb_name) 
        then (Some ((BigBlock bb_name cmds None None), (convert_list_to_cont ( bbs) cont))) 
        else (find_label lbl bbs cont))" 
  | "find_label lbl ((BigBlock bb_name cmds (Some (ParsedIf guard then_bbs else_bbs)) None) # bbs) cont = 
      (if (Some lbl = bb_name) 
        then (Some ((BigBlock bb_name cmds (Some (ParsedIf guard then_bbs else_bbs)) None), (convert_list_to_cont ( bbs) cont))) 
        else (if (find_label lbl then_bbs cont \<noteq> None) 
                then (find_label lbl (then_bbs @ bbs) cont) 
                else (find_label lbl (else_bbs @ bbs) cont)))" 
  | "find_label lbl ((BigBlock bb_name cmds (Some (ParsedWhile guard invariants body_bbs)) None) # bbs) cont = 
      (if (Some lbl = bb_name) 
        then (Some ((BigBlock bb_name cmds (Some (ParsedWhile guard invariants body_bbs)) None), (convert_list_to_cont ( bbs) cont))) 
        else (if (find_label lbl body_bbs cont \<noteq> None) 
                then (find_label lbl body_bbs (convert_list_to_cont ((bbs)@[(BigBlock None [] (Some (ParsedWhile guard invariants body_bbs)) None)]) cont)) 
                else (find_label lbl bbs cont)))"  
  | "find_label lbl ((BigBlock bb_name cmds (Some (ParsedBreak n)) None) # bbs) cont = 
      (if (Some lbl = bb_name) 
        then (Some ((BigBlock bb_name cmds (Some (ParsedBreak n)) None), (convert_list_to_cont ( bbs) cont))) 
        else (find_label lbl bbs cont))" 
  | "find_label lbl ((BigBlock bb_name cmds (Some (WhileWrapper while_loop)) None) # bbs) cont = 
      find_label lbl ((BigBlock bb_name cmds (Some while_loop) None) # bbs) cont"
  | "find_label lbl ((BigBlock bb_name cmds None (Some transfer_stmt)) # bbs) cont = 
      (if (Some lbl = bb_name) 
        then (Some ((BigBlock bb_name cmds None (Some transfer_stmt)), (convert_list_to_cont ( bbs) cont))) 
        else (find_label lbl bbs cont))"
  | "find_label lbl ((BigBlock bb_name cmds (Some s) (Some t)) # bbs) cont = None"

fun get_state :: "('a, 'm) ast_config \<Rightarrow> ('a, 'm) state"
  where
    "get_state (bb, cont, s1) = s1"

fun is_final :: "('a, 'm) ast_config \<Rightarrow> bool" 
  where
    "is_final ((BigBlock bb_name [] None None), KStop, s1) = True"
  | "is_final other = False"

text \<open>Small-step semantics\<close>

locale ast =
  fixes map_select :: "('a::absval, 'm::mapval) val \<Rightarrow> ('a, 'm) val \<Rightarrow> ('a, 'm) val"
  fixes map_store  :: "('a, 'm) val \<Rightarrow> ('a, 'm) val \<Rightarrow> ('a, 'm) val \<Rightarrow> ('a, 'm) val"
begin

interpretation semantics map_select map_store .

inductive red_bigblock :: "'p proc_context \<Rightarrow> var_context \<Rightarrow> ('a, 'm) fun_interp \<Rightarrow> rtype_env  \<Rightarrow> ast \<Rightarrow> ('a, 'm) ast_config \<Rightarrow> ('a, 'm) ast_config \<Rightarrow> bool" 
  ("_,_,_,_,_ \<turnstile> (\<langle>_\<rangle> \<longrightarrow>/ _)" [51,0,0,0] 81)
  for M :: "'p proc_context" and \<Lambda> :: var_context and \<Gamma> :: "('a, 'm) fun_interp" and \<Omega> :: rtype_env and T :: ast
  where
    RedSimpleCmds: 
    "\<lbrakk>(M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs, (Normal n_s)\<rangle> [\<rightarrow>] s1) \<and> (cs \<noteq> Nil) \<rbrakk> 
      \<Longrightarrow> M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> \<langle>((BigBlock bb_name cs str_cmd tr_cmd), cont0, Normal n_s)\<rangle> \<longrightarrow> 
                              ((BigBlock bb_name [] str_cmd tr_cmd), cont0, s1)"  

  | RedFailure_or_Magic: 
    "\<lbrakk> (s1 = Magic) \<or> (s1 = Failure); \<not> (is_final ((BigBlock bb_name [] str_cmd tr_cmd), cont0, s1))  \<rbrakk> 
      \<Longrightarrow> M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> \<langle>((BigBlock bb_name [] str_cmd tr_cmd), cont0, s1)\<rangle> \<longrightarrow> 
                          ((BigBlock bb_name [] None None), KStop, s1)"

  | RedSkip: 
    "M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> \<langle>((BigBlock bb_name [] None None), (KSeq b cont0), Normal n_s)\<rangle> \<longrightarrow> 
                    (b, cont0, Normal n_s)"

  | RedSkipEndBlock: 
    "M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> \<langle>((BigBlock bb_name [] None None),  (KEndBlock cont0),  Normal n_s)\<rangle> \<longrightarrow> 
                    ((BigBlock bb_name [] None None), cont0, Normal n_s)"

  | RedReturn: 
    "M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> \<langle>(BigBlock bb_name [] None (Some Return), cont0, Normal n_s)\<rangle> \<longrightarrow> 
                          ((BigBlock bb_name [] None None), KStop, Normal n_s)"

  | RedParsedIfTrue: 
    "\<lbrakk>\<And> b. bb_guard = (Some b) \<Longrightarrow>  \<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>b, n_s\<rangle> \<Down> LitV (LBool True) \<rbrakk>  
        \<Longrightarrow> M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> \<langle>((BigBlock bb_name [] 
                                (Some (ParsedIf bb_guard (then_hd # then_bbs) elsebigblocks)) None), cont0, Normal n_s)\<rangle> \<longrightarrow> 
                            (then_hd, (convert_list_to_cont ( then_bbs) cont0), Normal n_s)"

  | RedParsedIfFalse: 
    "\<lbrakk>\<And>b. bb_guard = (Some b) \<Longrightarrow>  \<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>b, n_s\<rangle> \<Down> LitV (LBool False) \<rbrakk> 
        \<Longrightarrow> M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> \<langle>((BigBlock bb_name []
                                (Some (ParsedIf bb_guard thenbigblocks (else_hd # else_bbs))) None), cont0, Normal n_s)\<rangle> \<longrightarrow>
                            (else_hd, (convert_list_to_cont ( else_bbs) cont0), Normal n_s)"

  | RedParsedWhileWrapper: 
    "M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> 
      \<langle>((BigBlock bb_name [] 
              (Some (WhileWrapper str)) None), cont0,  Normal n_s)\<rangle> \<longrightarrow>
        ((BigBlock bb_name [] 
                (Some str) None), (KEndBlock cont0),  Normal n_s)"
 
  | RedParsedWhile_InvFail: 
    "\<lbrakk>\<And> b. bb_guard = (Some b) \<Longrightarrow> \<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>b, n_s\<rangle> \<Down> LitV (LBool True); 
       bb_invariants = invs1@[I]@invs2;
       expr_all_sat \<Lambda> \<Gamma> \<Omega> n_s invs1;
       \<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>I, n_s\<rangle> \<Down> BoolV False \<rbrakk> 
       \<Longrightarrow> M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> 
           \<langle>((BigBlock bb_name [] 
                    (Some (ParsedWhile bb_guard bb_invariants (bb_hd # body_bbs))) None), cont0,  Normal n_s)\<rangle> \<longrightarrow> 
              ((BigBlock bb_name [] None None), KStop, Failure)"

  | RedParsedWhileTrue: 
    "\<lbrakk>\<And> b.  bb_guard = (Some b) \<Longrightarrow> \<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>b, n_s\<rangle> \<Down> LitV (LBool True); 
       (expr_all_sat \<Lambda> \<Gamma> \<Omega> n_s bb_invariants) \<rbrakk> 
       \<Longrightarrow> M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> 
            \<langle>((BigBlock bb_name [] 
                     (Some (ParsedWhile bb_guard bb_invariants (bb_hd # body_bbs))) None), cont0,  Normal n_s)\<rangle> \<longrightarrow> 
              (bb_hd, convert_list_to_cont ((body_bbs)@[(BigBlock bb_name [] (Some (ParsedWhile bb_guard bb_invariants (bb_hd # body_bbs))) None)]) cont0, Normal n_s)"


  | RedParsedWhileFalse: 
    "\<lbrakk>\<And> b. bb_guard = (Some b) \<Longrightarrow> \<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>b, n_s\<rangle> \<Down> LitV (LBool False);
       (expr_all_sat \<Lambda> \<Gamma> \<Omega> n_s bb_invariants) \<rbrakk>  
       \<Longrightarrow> M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> \<langle>((BigBlock bb_name [] 
                                (Some (ParsedWhile bb_guard bb_invariants bigblocks)) None), cont0, Normal n_s)\<rangle> \<longrightarrow> 
                          ((BigBlock bb_name [] None None), cont0, Normal n_s)"

  | RedBreak0: 
    "M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> \<langle>((BigBlock bb_name [] (Some (ParsedBreak 0)) None), (KEndBlock cont0), Normal n_s)\<rangle> \<longrightarrow> 
                          ((BigBlock bb_name [] None None), cont0, Normal n_s)"

  | RedBreakN: 
    "M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> 
           \<langle>((BigBlock bb_name [] (Some (ParsedBreak n)) None), (KSeq b cont0), Normal n_s)\<rangle> \<longrightarrow> 
            ((BigBlock None [] (Some (ParsedBreak n)) None), cont0, Normal n_s)"

  | RedBreakNPlus1: 
    "M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> 
           \<langle>((BigBlock bb_name [] (Some (ParsedBreak (n + 1))) None), (KEndBlock cont0), Normal n_s)\<rangle> \<longrightarrow> 
            ((BigBlock None [] (Some (ParsedBreak n)) None), cont0, Normal n_s)"

  | RedGoto: 
    "\<lbrakk> (find_label label T KStop) = Some (found_bigblock, found_cont) \<rbrakk> 
        \<Longrightarrow> M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> \<langle>((BigBlock bb_name [] None (Some (Goto label))), cont0, Normal n_s)\<rangle> \<longrightarrow> 
                            (found_bigblock, found_cont, (Normal n_s))"

abbreviation red_bigblock_k_step :: "'p proc_context \<Rightarrow> var_context \<Rightarrow> ('a, 'm) fun_interp \<Rightarrow> rtype_env \<Rightarrow> ast \<Rightarrow> ('a, 'm) ast_config \<Rightarrow> nat \<Rightarrow> ('a, 'm) ast_config \<Rightarrow> bool"
  ("_,_,_,_,_ \<turnstile>_ -n\<longrightarrow>^_/ _" [51,0,0,0,0] 81)
where "red_bigblock_k_step M \<Lambda> \<Gamma> \<Omega> T c1 n c2 \<equiv> ((red_bigblock M \<Lambda> \<Gamma> \<Omega> T)^^n) c1 c2"

subsection \<open>Procedure Correctness\<close>

text\<open>defining correctness of the AST\<close>

fun convert_ast_to_program_point :: "ast \<Rightarrow> bigblock \<times> cont" where
    "convert_ast_to_program_point [] = ((BigBlock None [] None None), KStop)"
  | "convert_ast_to_program_point (b#bs) = (b, convert_list_to_cont bs KStop)"

fun init_ast :: "ast \<Rightarrow> ('a, 'm) nstate \<Rightarrow> ('a, 'm) ast_config"
  where
    "init_ast [] ns1 = ((BigBlock None [] None None), KStop, Normal ns1)"
  | "init_ast (b#bbs) ns1 = (b, convert_list_to_cont ( bbs) KStop, Normal ns1)"

definition valid_configuration 
  where "valid_configuration \<Lambda> \<Gamma> \<Omega> posts bb cont state \<equiv> 
         state \<noteq> Failure \<and> 
         (is_final (bb, cont, state) \<longrightarrow> (\<forall>ns'. state = Normal ns' \<longrightarrow> expr_all_sat \<Lambda> \<Gamma> \<Omega> ns' posts))"

definition proc_body_satisfies_spec :: "'p proc_context \<Rightarrow> var_context \<Rightarrow> ('a, 'm) fun_interp \<Rightarrow> rtype_env \<Rightarrow> expr list \<Rightarrow> expr list \<Rightarrow> ast \<Rightarrow> ('a, 'm) nstate \<Rightarrow> bool"
  where "proc_body_satisfies_spec M \<Lambda> \<Gamma> \<Omega> pres posts ast ns \<equiv>
         expr_all_sat \<Lambda> \<Gamma> \<Omega> ns pres \<longrightarrow> 
          (\<forall> bb cont state. (rtranclp (red_bigblock M \<Lambda> \<Gamma> \<Omega> ast) (init_ast ast ns) (bb, cont, state)) \<longrightarrow> 
                    valid_configuration \<Lambda> \<Gamma> \<Omega> posts bb cont state)"

fun proc_all_pres :: "ast procedure \<Rightarrow> expr list"
  where "proc_all_pres p = map fst (proc_pres p)"

fun proc_checked_posts :: "ast procedure \<Rightarrow> expr list"
  where "proc_checked_posts p = map fst (filter (\<lambda>x. \<not> snd(x)) (proc_posts p))"

end

end