
section propositional

variables P Q R : Prop


------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P  :=
begin
  intro h,
  intro g,
  contradiction,
end

theorem doubleneg_elim :
  ¬¬P → P  :=
begin
  intro h,
  by_contradiction hboom,
  have hq : false := h hboom,
  assumption,
end

theorem doubleneg_law :
  ¬¬P ↔ P  :=
begin
  split,
  intro h,
    by_contradiction hboom,
    have hp : false := h hboom,
    assumption,
  intro h,
    intro g,
    contradiction,
end

------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  :=
begin
  intro h,
  cases h with hp hq,

  right,
  assumption,

  left,
  assumption,
end

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  :=
begin
  intro h,
  cases h with hp hq,
  split,
  repeat {assumption},
end


------------------------------------------------
-- Proposições de interdefinabilidade dos →,∨:
------------------------------------------------

theorem impl_as_disj_converse :
  (¬P ∨ Q) → (P → Q)  :=
begin
  intro h,
  intro hp,
  cases h,
  contradiction,
  assumption,
end

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  :=
begin
  intro h,
  intro hnp,
  cases h,
  contradiction,
  assumption,
end


------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  :=
begin
  intro h,
  intro hq,
  intro nq,
  have hpq: Q := h nq,
  contradiction,
end

theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  :=
begin
  intro h,
  intro hp,
  by_contradiction hboom,
  have hpq: ¬P := h hboom,
  contradiction,
end

theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  :=
begin
  split,
  intro h,
    intro hq,
    intro nq,
    have hpq: Q := h nq,
    contradiction,
  intro h,
    intro hp,
    by_contradiction hboom,
    have hpq: ¬P := h hboom,
    contradiction,
end


------------------------------------------------
-- A irrefutabilidade do LEM:
------------------------------------------------

theorem lem_irrefutable :
  ¬¬(P∨¬P)  :=
begin
  intro h,
  apply h,
  by_cases P,
  left,
  assumption,
  right,
  assumption,
end


------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  :=
begin
  intro h,
  intro hp,
  apply hp,
  apply h,
  intro hpq,
  contradiction,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  :=
begin
  intro h,
  intro hnpnq,
  cases h with hp hq,
  cases hnpnq,
  contradiction,
  cases hnpnq,
  contradiction,
end

theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  :=
begin
  intro h,
  intro hp,
  cases h,
  cases hp,
  repeat {contradiction},
end


------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_disj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  :=
begin
  intro h,
  split,
  intro hp,
  apply h,
  left,
  assumption,

  intro hq,
  apply h,
  right,
  assumption,
end

theorem demorgan_disj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  :=
begin
  intro h,
  cases h,
  intro hpq,
  cases hpq,
  repeat {contradiction},
end

theorem demorgan_conj :
  ¬(P∧Q) → (¬Q ∨ ¬P)  :=
begin
  sorry,
end

theorem demorgan_conj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  :=
begin
  intro h,
  cases h,
  intro hpq,
    cases hpq with hp hq,
    contradiction,
  intro hpq,
    cases hpq with hp hq,
    contradiction,
end

theorem demorgan_conj_law :
  ¬(P∧Q) ↔ (¬Q ∨ ¬P)  :=
begin
  sorry,
end

theorem demorgan_disj_law :
  ¬(P∨Q) ↔ (¬P ∧ ¬Q)  :=
begin
  split,
  intro h,
  split,
  intro hp,
    apply h,
    left,
    assumption,
  intro hq,
    apply h,
    right,
    assumption,
  intro h,
  cases h,
  intro hpq,
  cases hpq,
  repeat {contradiction},
end

------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
------------------------------------------------

theorem distr_conj_disj :
  P∧(Q∨R) → (P∧Q)∨(P∧R)  :=
begin
  intro h,
  cases h with hp hqr,
  cases hqr,
  left,
  split,
  repeat {assumption},
  right,
  split,
  repeat {assumption},
end

theorem distr_conj_disj_converse :
  (P∧Q)∨(P∧R) → P∧(Q∨R)  :=
begin
  intro h,
  split,
  cases h,
  repeat {
    cases h with hp hq,
    assumption
  },
  cases h,
  left,
  cases h with hp hq,
  assumption,
  right,
  cases h with hq hr,
  assumption,
end

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
begin
  intro h,
  split,
  cases h,
    left,
    assumption,
    right,
    cases h with hq hr,
    assumption,
  cases h,
    left,
    assumption,
    right,
    cases h with hq hr,
    assumption,
end

theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  :=
begin
  intro h,
  cases h with hpq hqr,
  cases hpq,
  left,
  assumption,

  cases hqr,
  left,
  assumption,
  right,
  split,
  repeat {assumption},

end


------------------------------------------------
-- Currificação
------------------------------------------------

theorem curry_prop :
  ((P∧Q)→R) → (P→(Q→R))  :=
begin
  intro h,
  intro hp,
  intro hq,
  apply h,
  split,
  repeat {assumption},
end

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  :=
begin
  intro h,
  intro hpq,
  apply h,
  repeat {
    cases hpq with hp hq,
    assumption
  },
end


------------------------------------------------
-- Reflexividade da →:
------------------------------------------------

theorem impl_refl :
  P → P  :=
begin
  intro h,
  assumption,
end

------------------------------------------------
-- Weakening and contraction:
------------------------------------------------

theorem weaken_disj_right :
  P → (P∨Q)  :=
begin
  intro h,
  left,
  assumption,
end

theorem weaken_disj_left :
  Q → (P∨Q)  :=
begin
  intro h,
  right,
  assumption,
end

theorem weaken_conj_right :
  (P∧Q) → P  :=
begin
  intro h,
  cases h with hp hq,
  assumption,
end

theorem weaken_conj_left :
  (P∧Q) → Q  :=
begin
  intro h,
  cases h with hp hq,
  assumption,
end

theorem conj_idempot :
  (P∧P) ↔ P :=
begin
  split,
  intro h,
    cases h,
    assumption,
  intro h,
  split,
  repeat {assumption},
end

theorem disj_idempot :
  (P∨P) ↔ P  :=
begin
  split,
  intro h,
    cases h,
    repeat {assumption},
  intro h,
  left,
  assumption,
end

end propositional


----------------------------------------------------------------


section predicate

variable U : Type
variables P Q : U -> Prop


------------------------------------------------
-- As leis de De Morgan para ∃,∀:
------------------------------------------------

theorem demorgan_exists :
  ¬(∃x, P x) → (∀x, ¬P x)  :=
begin
  intro h,
  intro u,
  intro hp,
  apply h,
  existsi u,
  assumption,
end

theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
begin
  intro h,
  intro hp,
  cases hp with u hu,
  apply h u,
  assumption,
end

theorem demorgan_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  :=
begin
  intro h,
  by_contradiction hboom,
  apply h,
  intro u,
  by_contra,
  apply hboom,
  existsi u,
  assumption,
end

theorem demorgan_forall_converse :
  (∃x, ¬P x) → ¬(∀x, P x)  :=
begin
  intro h,
  intro hp,
  cases h with u hu,
  apply hu,
  apply hp u,
end

theorem demorgan_forall_law :
  ¬(∀x, P x) ↔ (∃x, ¬P x)  :=
begin
  split,
  intro h,
    by_contradiction hboom,
    apply h,
    intro u,
    by_contra,
    apply hboom,
    existsi u,
    assumption,
  intro h,
  intro n_forall,
  cases h with u hu,
  apply hu,
  apply n_forall,
end

theorem demorgan_exists_law :
  ¬(∃x, P x) ↔ (∀x, ¬P x)  :=
begin
  split,
  intro h,
    intro u,
    intro hp,
    apply h,
    existsi u,
    assumption,
  intro h,
    intro hp,
    cases hp with u hu,
    apply h u,
    assumption,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∃,∀:
------------------------------------------------

theorem exists_as_neg_forall :
  (∃x, P x) → ¬(∀x, ¬P x)  :=
begin
  intro h,
  intro hp,
  cases h with u hu,
  apply hp u,
  assumption,
end

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
begin
  intro h,
  intro hp,
  cases hp with u hu,
  apply hu,
  apply h u,
end

theorem forall_as_neg_exists_converse :
  ¬(∃x, ¬P x) → (∀x, P x)  :=
begin
  intro h,
  intro u,
  by_contradiction hboom,
  apply h,
  existsi u,
  assumption,
end

theorem exists_as_neg_forall_converse :
  ¬(∀x, ¬P x) → (∃x, P x)  :=
begin
  intro h,
  by_contradiction hboom,
  apply h,
  intro u,
  intro pu,
  apply hboom,
  existsi u,
  assumption,
end

theorem forall_as_neg_exists_law :
  (∀x, P x) ↔ ¬(∃x, ¬P x)  :=
begin
  split,
  intro h,
    intro hexist,
    cases hexist with u hu,
    apply hu,
    apply h,
  intro h,
    intro u,
    by_contradiction hboom,
    apply h,
    existsi u,
    assumption,
end

theorem exists_as_neg_forall_law :
  (∃x, P x) ↔ ¬(∀x, ¬P x)  :=
begin
  split,
  intro h,
    intro n_forall,
    cases h with u hu,
    apply n_forall u,
    assumption,
  intro h,
    by_contradiction hboom,
    apply h,
    intro u,
    intro pu,
    apply hboom,
    existsi u,
    assumption,
end


------------------------------------------------
--  Proposições de distributividade de quantificadores:
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃x, P x ∧ Q x) → (∃x, P x) ∧ (∃x, Q x)  :=
begin
  intro h,
  cases h with u hu,
  cases hu with hp hq,
  split,
  repeat {
    existsi u,
    assumption,
  },

end

theorem exists_disj_as_disj_exists :
  (∃x, P x ∨ Q x) → (∃x, P x) ∨ (∃x, Q x)  :=
begin
  intro h,
  cases h with u hu,
  cases hu with hp hq,
  left,
  existsi u,
  assumption,
  right,
  existsi u,
  assumption,
end

theorem exists_disj_as_disj_exists_converse :
  (∃x, P x) ∨ (∃x, Q x) → (∃x, P x ∨ Q x)  :=
begin
  intro h,
  cases h,
  repeat {
    cases h with u hu,
    existsi u,
  },
  left,
  assumption,
  right,
  assumption,
end

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  :=
begin
  sorry,
end

theorem forall_conj_as_conj_forall_converse :
  (∀x, P x) ∧ (∀x, Q x) → (∀x, P x ∧ Q x)  :=
begin
  intro h,
  intro u,
  cases h with hp hq,
  split,
  apply hp,
  apply hq,
end


theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  :=
begin
  intro h,
  intro u,
  cases h,
  left, 
  apply h,
  right,
  apply h,
end


/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
  (∀x, P x ∨ Q x) → (∀x, P x) ∨ (∀x, Q x)  :=
begin
end

theorem exists_conj_as_conj_exists_converse :
  (∃x, P x) ∧ (∃x, Q x) → (∃x, P x ∧ Q x)  :=
begin
end

---------------------------------------------- -/

end predicate
