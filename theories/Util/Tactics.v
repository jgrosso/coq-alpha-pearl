Tactic Notation "intro_all" := repeat intro.

Tactic Notation "inverts" hyp(H) := inversion H; subst; clear H.

Tactic Notation "gen_dep" ident(x) :=
  generalize dependent x.
Tactic Notation "gen_dep" ident(x) ident(y) :=
  gen_dep x; gen_dep y.
Tactic Notation "gen_dep" ident(x) ident(y) ident(z) :=
  gen_dep x; gen_dep y; gen_dep z.
Tactic Notation "gen_dep" ident(x) ident(y) ident(z) ident(a) :=
  gen_dep x; gen_dep y; gen_dep z; gen_dep a.
Tactic Notation "gen_dep" ident(x) ident(y) ident(z) ident(a) ident(b) :=
  gen_dep x; gen_dep y; gen_dep z; gen_dep a; gen_dep b.
Tactic Notation "gen_dep" ident(x) ident(y) ident(z) ident(a) ident(b) ident(c) :=
  gen_dep x; gen_dep y; gen_dep z; gen_dep a; gen_dep b; gen_dep c.
Tactic Notation "gen_dep" ident(x) ident(y) ident(z) ident(a) ident(b) ident(c) ident(d) :=
  gen_dep x; gen_dep y; gen_dep z; gen_dep a; gen_dep b; gen_dep c; gen_dep d.
Tactic Notation "gen_dep" ident(x) ident(y) ident(z) ident(a) ident(b) ident(c) ident(d) ident(e) :=
  gen_dep x; gen_dep y; gen_dep z; gen_dep a; gen_dep b; gen_dep c; gen_dep d; gen_dep e.
Tactic Notation "gen_dep" ident(x) ident(y) ident(z) ident(a) ident(b) ident(c) ident(d) ident(e) ident(f) :=
  gen_dep x; gen_dep y; gen_dep z; gen_dep a; gen_dep b; gen_dep c; gen_dep d; gen_dep e; gen_dep f.
Tactic Notation "gen_dep" ident(x) ident(y) ident(z) ident(a) ident(b) ident(c) ident(d) ident(e) ident(f) ident(g) :=
  gen_dep x; gen_dep y; gen_dep z; gen_dep a; gen_dep b; gen_dep c; gen_dep d; gen_dep e; gen_dep f; gen_dep g.
Tactic Notation "gen_dep" ident(x) ident(y) ident(z) ident(a) ident(b) ident(c) ident(d) ident(e) ident(f) ident(g) ident(h) :=
  gen_dep x; gen_dep y; gen_dep z; gen_dep a; gen_dep b; gen_dep c; gen_dep d; gen_dep e; gen_dep f; gen_dep g; gen_dep h.
