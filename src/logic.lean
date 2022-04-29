
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
  exact hq,
end

theorem doubleneg_law :
  ¬¬P ↔ P  :=
begin
  split,
  apply doubleneg_elim,
  apply doubleneg_intro,
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
  exact hp,

  left,
  exact hq,
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
  exact h,
end

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  :=
begin
  intro h,
  intro hnp,
  cases h,
  contradiction,
  exact h,
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
  apply impl_as_contrapositive,
  apply impl_as_contrapositive_converse,
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
  exact h,
  right,
  exact h,
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
  exact hp,

  intro hq,
  apply h,
  right,
  exact hq,
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
  intro h,
  by_cases hp: P,
  left,
  intro hq,
  apply h,
  apply and.intro hp hq,
  right,
  exact hp,
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
  split,
  apply demorgan_conj,
  apply demorgan_conj_converse,
end

theorem demorgan_disj_law :
  ¬(P∨Q) ↔ (¬P ∧ ¬Q)  :=
begin
  split,
  apply demorgan_disj,
  apply demorgan_disj_converse,
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
    exact hp,
  },
  cases h,
  left,
  cases h with hp hq,
  exact hq,
  right,
  cases h with hq hr,
  exact hr,
end

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
begin
  intro h,
  split,
  repeat {
    cases h,
    left,
    exact h,
    right,
    cases h with hq hr,
    assumption,
  }
end

theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  :=
begin
  intro h,
  cases h with hpq hqr,
  cases hpq,
  left,
  exact hpq,

  cases hqr,
  left,
  exact hqr,
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
  exact h,
end

------------------------------------------------
-- Weakening and contraction:
------------------------------------------------

theorem weaken_disj_right :
  P → (P∨Q)  :=
begin
  intro h,
  left,
  exact h,
end

theorem weaken_disj_left :
  Q → (P∨Q)  :=
begin
  intro h,
  right,
  exact h,
end

theorem weaken_conj_right :
  (P∧Q) → P  :=
begin
  intro h,
  cases h with hp hq,
  exact hp,
end

theorem weaken_conj_left :
  (P∧Q) → Q  :=
begin
  intro h,
  cases h with hp hq,
  exact hq,
end

theorem conj_idempot :
  (P∧P) ↔ P :=
begin
  split,
  intro h,
    cases h,
    exact h_left,
  intro h,
  split,
  repeat {exact h},
end

theorem disj_idempot :
  (P∨P) ↔ P  :=
begin
  split,
  intro h,
    cases h,
    repeat {exact h},
  intro h,
  left,
  exact h,
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
  exact hp,
end

theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
begin
  intro h,
  intro hp,
  cases hp with u hu,
  apply h u,
  exact hu,
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
  exact h,
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
  apply demorgan_forall,
  apply demorgan_forall_converse,
end

theorem demorgan_exists_law :
  ¬(∃x, P x) ↔ (∀x, ¬P x)  :=
begin
  split,
  apply demorgan_exists,
  apply demorgan_exists_converse,
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
  exact hu,
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
  exact hboom,
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
  exact pu,
end

theorem forall_as_neg_exists_law :
  (∀x, P x) ↔ ¬(∃x, ¬P x)  :=
begin
  split,
  apply forall_as_neg_exists,
  apply forall_as_neg_exists_converse,
end

theorem exists_as_neg_forall_law :
  (∃x, P x) ↔ ¬(∀x, ¬P x)  :=
begin
  split,
  apply exists_as_neg_forall,
  apply exists_as_neg_forall_converse,
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
  exact hp,
  right,
  existsi u,
  exact hq,
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
  exact hu,
  right,
  exact hu,
end

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  :=
begin
  intro h,
  split,
  intro u,
  apply (h u).left,
  intro v,
  apply (h v).right,
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
