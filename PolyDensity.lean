/-
  A negative answer to the 5/6-Poly-Density Question.

  Biktairov, Gąsieniec, Jiamjitrak, Namrata, Smith, Wild,
  "Simple approximation algorithms for Polyamorous Scheduling", arXiv:2411.06292, Section 6:
    "Question 6.1 (5/6-Poly-Density Question): Does every Decision Poly Scheduling instance
     with poly density d ≤ 5/6 admit a schedule?"

  Answer: no.  The polycule `gadget X` (a triangle 0-1-2 with pendant edges 0-3 and 1-4,
  frequencies f(01) = X, f(02) = 4, f(03) = 2, f(12) = 4, f(14) = 2) is infeasible for every X ≥ 1
  and has poly density exactly 3/4 + 1/X.  For X = 13 the density is 43/52 < 5/6, and
  as X → ∞ the density tends to 3/4.
-/
import Mathlib

open Finset

namespace PolySched

/-- A Decision Polyamorous Scheduling instance (Definition 2.2 of arXiv:2411.06292):
a simple undirected graph whose edges are indexed by `ι` (edge `e` joins `src e` and `dst e`),
with positive integer frequencies `f`. -/
structure DPS (V ι : Type) where
  src : ι → V
  dst : ι → V
  loopless : ∀ e, src e ≠ dst e
  simple : ∀ e e', s(src e, dst e) = s(src e', dst e') → e = e'
  f : ι → ℕ
  f_pos : ∀ e, 0 < f e

variable {V ι : Type}

/-- Two edges share an endpoint. -/
def DPS.Adjacent (I : DPS V ι) (e e' : ι) : Prop :=
  I.src e = I.src e' ∨ I.src e = I.dst e' ∨ I.dst e = I.src e' ∨ I.dst e = I.dst e'

/-- A matching: a set of pairwise non-adjacent edges. -/
def DPS.IsMatching (I : DPS V ι) (M : Finset ι) : Prop :=
  ∀ e ∈ M, ∀ e' ∈ M, e ≠ e' → ¬ I.Adjacent e e'

/-- An inclusion-maximal matching. -/
def DPS.IsMaximalMatching (I : DPS V ι) (M : Finset ι) : Prop :=
  I.IsMatching M ∧ ∀ M' : Finset ι, I.IsMatching M' → M ⊆ M' → M' = M

/-- `S` is a valid schedule (Definition 2.2): every day is a matching, and the recurrence time
`r_S(e) = sup { d+1 | ∃ t, e ∉ S(t) ∪ … ∪ S(t+d-1) }` (eq. (1)) is at most `f e`; unfolded, every
`d` for which some window of `d` consecutive days misses `e` satisfies `d + 1 ≤ f e`. -/
def DPS.IsSchedule (I : DPS V ι) (S : ℕ → Finset ι) : Prop :=
  (∀ t, I.IsMatching (S t)) ∧
    ∀ e d, (∃ t, ∀ i < d, e ∉ S (t + i)) → d + 1 ≤ I.f e

def DPS.Schedulable (I : DPS V ι) : Prop := ∃ S, I.IsSchedule S

/-- The weightings `Z` of Definition 4.4: `z e ∈ [0,1]`, `∑ z e = 1`. -/
def IsWeighting [Fintype ι] (z : ι → ℝ) : Prop :=
  (∀ e, 0 ≤ z e ∧ z e ≤ 1) ∧ ∑ e, z e = 1

/-- `max_{M ∈ 𝓜} ∑_{e ∈ M} z_e · f_e`, over inclusion-maximal matchings `M`. -/
noncomputable def DPS.matchVal (I : DPS V ι) (z : ι → ℝ) : ℝ :=
  ⨆ M : {M : Finset ι // I.IsMaximalMatching M}, ∑ e ∈ M.1, z e * I.f e

/-- Poly density (Definition 4.4): `d = max_{z ∈ Z} 1 / max_{M ∈ 𝓜} ∑_{e ∈ M} z_e f_e`. -/
noncomputable def DPS.polyDensity [Fintype ι] (I : DPS V ι) : ℝ :=
  sSup {r : ℝ | ∃ z, IsWeighting z ∧ r = 1 / I.matchVal z}

/-! ### The gadget -/

/-- Edges: 0 = {0,1} (freq X), 1 = {0,2} (freq 4), 2 = {0,3} (freq 2),
3 = {1,2} (freq 4), 4 = {1,4} (freq 2). -/
def gsrc : Fin 5 → Fin 5 := ![0, 0, 0, 1, 1]
def gdst : Fin 5 → Fin 5 := ![1, 2, 3, 2, 4]
def gf (X : ℕ) : Fin 5 → ℕ := ![X, 4, 2, 4, 2]

def gadget (X : ℕ) (hX : 0 < X) : DPS (Fin 5) (Fin 5) where
  src := gsrc
  dst := gdst
  loopless := by decide
  simple := by decide
  f := gf X
  f_pos := by intro e; fin_cases e <;> simp [gf, hX]

/-- Adjacency in the gadget does not depend on `X`; it is decidable. -/
lemma gadget_adj (X : ℕ) (hX : 0 < X) (e e' : Fin 5) :
    (gadget X hX).Adjacent e e' ↔
      (gsrc e = gsrc e' ∨ gsrc e = gdst e' ∨ gdst e = gsrc e' ∨ gdst e = gdst e') := Iff.rfl

lemma gadget_matching (X : ℕ) (hX : 0 < X) (M : Finset (Fin 5)) :
    (gadget X hX).IsMatching M ↔
      ∀ e ∈ M, ∀ e' ∈ M, e ≠ e' →
        ¬ (gsrc e = gsrc e' ∨ gsrc e = gdst e' ∨ gdst e = gsrc e' ∨ gdst e = gdst e') := Iff.rfl

/-! ### Infeasibility -/

theorem gadget_infeasible (X : ℕ) (hX : 0 < X) : ¬ (gadget X hX).Schedulable := by
  rintro ⟨S, hM, hR⟩
  -- every window of `f e` consecutive days contains `e`
  have hw : ∀ e t, ∃ s, t ≤ s ∧ s < t + gf X e ∧ e ∈ S s := by
    intro e t
    by_contra h
    push Not at h
    have := hR e (gf X e) ⟨t, fun i hi hmem => (h (t + i) (by omega) (by omega)) hmem⟩
    change gf X e + 1 ≤ gf X e at this
    omega
  -- conflicting edges cannot share a day
  have conf : ∀ t (a b : Fin 5), a ≠ b →
      (gsrc a = gsrc b ∨ gsrc a = gdst b ∨ gdst a = gsrc b ∨ gdst a = gdst b) →
      a ∈ S t → b ∈ S t → False := fun t a b hab hadj ha hb => hM t a ha b hb hab hadj
  obtain ⟨s, hs1, -, h0⟩ := hw 0 1
  obtain ⟨u, rfl⟩ : ∃ u, s = u + 1 := ⟨s - 1, by omega⟩
  -- pendant edges 2 = {0,3} and 4 = {1,4} (frequency 2) occupy days u and u+2
  have p2 : ∀ t, (t = u ∨ t = u + 2) → 2 ∈ S t := by
    rintro t (rfl | rfl)
    · obtain ⟨r, hr1, hr2, hr⟩ := hw 2 t
      simp [gf] at hr2
      rcases (show r = t ∨ r = t + 1 by omega) with rfl | rfl
      · exact hr
      · exact (conf _ 0 2 (by decide) (by decide) h0 hr).elim
    · obtain ⟨r, hr1, hr2, hr⟩ := hw 2 (u + 1)
      simp [gf] at hr2
      rcases (show r = u + 1 ∨ r = u + 2 by omega) with rfl | rfl
      · exact (conf _ 0 2 (by decide) (by decide) h0 hr).elim
      · exact hr
  have p4 : ∀ t, (t = u ∨ t = u + 2) → 4 ∈ S t := by
    rintro t (rfl | rfl)
    · obtain ⟨r, hr1, hr2, hr⟩ := hw 4 t
      simp [gf] at hr2
      rcases (show r = t ∨ r = t + 1 by omega) with rfl | rfl
      · exact hr
      · exact (conf _ 0 4 (by decide) (by decide) h0 hr).elim
    · obtain ⟨r, hr1, hr2, hr⟩ := hw 4 (u + 1)
      simp [gf] at hr2
      rcases (show r = u + 1 ∨ r = u + 2 by omega) with rfl | rfl
      · exact (conf _ 0 4 (by decide) (by decide) h0 hr).elim
      · exact hr
  -- edge 1 = {0,2} (frequency 4) is forced onto day u+3
  have q1 : 1 ∈ S (u + 3) := by
    obtain ⟨r, hr1, hr2, hr⟩ := hw 1 u
    simp [gf] at hr2
    rcases (show r = u ∨ r = u + 1 ∨ r = u + 2 ∨ r = u + 3 by omega) with rfl | rfl | rfl | rfl
    · exact (conf _ 1 2 (by decide) (by decide) hr (p2 _ (Or.inl rfl))).elim
    · exact (conf _ 0 1 (by decide) (by decide) h0 hr).elim
    · exact (conf _ 1 2 (by decide) (by decide) hr (p2 _ (Or.inr rfl))).elim
    · exact hr
  -- edge 3 = {1,2} (frequency 4) is forced onto day u+3
  have q3 : 3 ∈ S (u + 3) := by
    obtain ⟨r, hr1, hr2, hr⟩ := hw 3 u
    simp [gf] at hr2
    rcases (show r = u ∨ r = u + 1 ∨ r = u + 2 ∨ r = u + 3 by omega) with rfl | rfl | rfl | rfl
    · exact (conf _ 3 4 (by decide) (by decide) hr (p4 _ (Or.inl rfl))).elim
    · exact (conf _ 0 3 (by decide) (by decide) h0 hr).elim
    · exact (conf _ 3 4 (by decide) (by decide) hr (p4 _ (Or.inr rfl))).elim
    · exact hr
  -- but edges 1 and 3 share vertex 2
  exact conf _ 1 3 (by decide) (by decide) q1 q3

/-! ### Poly density of the gadget -/

/-- the matching predicate of the gadget, as a decidable predicate on `Finset (Fin 5)` -/
def gm (M : Finset (Fin 5)) : Prop :=
  ∀ e ∈ M, ∀ e' ∈ M, e ≠ e' →
    ¬ (gsrc e = gsrc e' ∨ gsrc e = gdst e' ∨ gdst e = gsrc e' ∨ gdst e = gdst e')

instance (M : Finset (Fin 5)) : Decidable (gm M) := by unfold gm; infer_instance

def gmax (M : Finset (Fin 5)) : Prop := gm M ∧ ∀ M' : Finset (Fin 5), gm M' → M ⊆ M' → M' = M

instance (M : Finset (Fin 5)) : Decidable (gmax M) := by unfold gmax; infer_instance

lemma gadget_maximal (X : ℕ) (hX : 0 < X) (M : Finset (Fin 5)) :
    (gadget X hX).IsMaximalMatching M ↔ gmax M := Iff.rfl

/-- every matching contains at most one of the three edges at vertex 0 -/
lemma gm_star (M : Finset (Fin 5)) (h : gm M) : (M.filter (fun e => e.val < 3)).card ≤ 1 := by
  revert M; decide

lemma gmax_A : gmax {0} := by decide
lemma gmax_B : gmax {1, 4} := by decide
lemma gmax_C : gmax {2, 3} := by decide
lemma gmax_D : gmax {2, 4} := by decide

lemma matchVal_ge (X : ℕ) (hX : 0 < X) (z : Fin 5 → ℝ) (M : Finset (Fin 5)) (hM : gmax M) :
    ∑ e ∈ M, z e * ((gf X e : ℕ) : ℝ) ≤ (gadget X hX).matchVal z := by
  unfold DPS.matchVal
  have hb : BddAbove (Set.range fun M : {M : Finset (Fin 5) // (gadget X hX).IsMaximalMatching M} =>
      ∑ e ∈ M.1, z e * ((gadget X hX).f e : ℝ)) := (Set.finite_range _).bddAbove
  exact le_ciSup (f := fun M : {M : Finset (Fin 5) // (gadget X hX).IsMaximalMatching M} =>
      ∑ e ∈ M.1, z e * ((gadget X hX).f e : ℝ)) hb ⟨M, hM⟩

/-- upper bound: every weighting has `1 / matchVal z ≤ 3/4 + 1/X` -/
lemma inv_matchVal_le (X : ℕ) (hX : 0 < X) (z : Fin 5 → ℝ) (hz : IsWeighting z) :
    1 / (gadget X hX).matchVal z ≤ 3 / 4 + 1 / (X : ℝ) := by
  have hXr : (0 : ℝ) < X := by exact_mod_cast hX
  set m := (gadget X hX).matchVal z
  have hA := matchVal_ge X hX z _ gmax_A
  have hB := matchVal_ge X hX z _ gmax_B
  have hC := matchVal_ge X hX z _ gmax_C
  have hD := matchVal_ge X hX z _ gmax_D
  simp [gf] at hA hB hC hD
  have hsum := hz.2
  simp [Fin.sum_univ_five] at hsum
  -- (1/X)·A + (1/4)(B + C + D) = ∑ z = 1
  have key : 1 ≤ (3 / 4 + 1 / (X : ℝ)) * m := by
    have h1 : z 0 ≤ m / X := by rw [le_div_iff₀ hXr]; linarith
    have : 1 / (X : ℝ) * m = m / X := by ring
    nlinarith
  have hm : 0 < m := by
    by_contra hneg; push Not at hneg
    have : (3 / 4 + 1 / (X : ℝ)) * m ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hneg
    linarith
  rw [div_le_iff₀ hm]; linarith

/-- the weighting concentrated on the three edges at vertex 0 -/
noncomputable def zstar (X : ℕ) : Fin 5 → ℝ :=
  let D : ℝ := 3 / 4 + 1 / (X : ℝ)
  ![1 / (X * D), 1 / (4 * D), 1 / (2 * D), 0, 0]

lemma zstar_weighting (X : ℕ) (hX : 0 < X) : IsWeighting (zstar X) := by
  have hXr : (0 : ℝ) < X := by exact_mod_cast hX
  have hD : (0 : ℝ) < 3 / 4 + 1 / (X : ℝ) := by positivity
  have hD' : (3 : ℝ) / 4 ≤ 3 / 4 + 1 / (X : ℝ) := by
    have : (0 : ℝ) ≤ 1 / (X : ℝ) := by positivity
    linarith
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
  refine ⟨?_, ?_⟩
  · intro e
    have hinv := mul_inv_cancel₀ hXr.ne'
    have hinv0 : (0 : ℝ) ≤ (X : ℝ)⁻¹ := by positivity
    fin_cases e <;> simp [zstar]
    all_goals
      refine ⟨by positivity, ?_⟩
      rw [← mul_inv]
      apply inv_le_one_of_one_le₀
      nlinarith
  · simp [zstar, Fin.sum_univ_five]
    field_simp
    ring

lemma zstar_term (X : ℕ) (hX : 0 < X) (e : Fin 5) :
    zstar X e * ((gf X e : ℕ) : ℝ) =
      if e.val < 3 then 1 / (3 / 4 + 1 / (X : ℝ)) else 0 := by
  have hXr : (0 : ℝ) < X := by exact_mod_cast hX
  have hD : (0 : ℝ) < 3 / 4 + 1 / (X : ℝ) := by positivity
  fin_cases e <;> simp [zstar, gf] <;> field_simp

lemma matchVal_zstar (X : ℕ) (hX : 0 < X) :
    (gadget X hX).matchVal (zstar X) = 1 / (3 / 4 + 1 / (X : ℝ)) := by
  have hXr : (0 : ℝ) < X := by exact_mod_cast hX
  have hD : (0 : ℝ) < 3 / 4 + 1 / (X : ℝ) := by positivity
  apply le_antisymm
  · unfold DPS.matchVal
    have : Nonempty {M : Finset (Fin 5) // (gadget X hX).IsMaximalMatching M} := ⟨⟨{0}, gmax_A⟩⟩
    apply ciSup_le
    rintro ⟨M, hM⟩
    change ∑ e ∈ M, zstar X e * ((gf X e : ℕ) : ℝ) ≤ _
    simp_rw [zstar_term X hX]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    have hc := gm_star M hM.1
    have : ((M.filter (fun e => e.val < 3)).card : ℝ) ≤ 1 := by exact_mod_cast hc
    have hpos : (0 : ℝ) ≤ 1 / (3 / 4 + 1 / (X : ℝ)) := by positivity
    nlinarith
  · have := matchVal_ge X hX (zstar X) {0} gmax_A
    simpa [zstar_term X hX] using this

/-- The poly density of the gadget is exactly `3/4 + 1/X`. -/
theorem gadget_polyDensity (X : ℕ) (hX : 0 < X) :
    (gadget X hX).polyDensity = 3 / 4 + 1 / (X : ℝ) := by
  have hXr : (0 : ℝ) < X := by exact_mod_cast hX
  have hD : (0 : ℝ) < 3 / 4 + 1 / (X : ℝ) := by positivity
  have hmem : 3 / 4 + 1 / (X : ℝ) ∈
      {r : ℝ | ∃ z, IsWeighting z ∧ r = 1 / (gadget X hX).matchVal z} :=
    ⟨zstar X, zstar_weighting X hX, by rw [matchVal_zstar X hX, one_div_one_div]⟩
  apply le_antisymm
  · apply csSup_le ⟨_, hmem⟩
    rintro r ⟨z, hz, rfl⟩
    exact inv_matchVal_le X hX z hz
  · apply le_csSup _ hmem
    refine ⟨3 / 4 + 1 / (X : ℝ), ?_⟩
    rintro r ⟨z, hz, rfl⟩
    exact inv_matchVal_le X hX z hz

/-! ### Main results -/

/-- **Answer to Question 6.1 of arXiv:2411.06292: no.**  Not every Decision Poly Scheduling
instance with poly density `d ≤ 5/6` admits a schedule. -/
theorem poly_density_question_false :
    ¬ ∀ (V ι : Type) [Fintype ι] (I : DPS V ι), I.polyDensity ≤ 5 / 6 → I.Schedulable := by
  intro h
  apply gadget_infeasible 13 (by norm_num)
  apply h
  rw [gadget_polyDensity]
  norm_num

/-- Stronger: for every `ε > 0` there is an infeasible instance with poly density in
`(3/4, 3/4 + ε)`, so no density threshold above `3/4` exists. -/
theorem infeasible_below (ε : ℝ) (hε : 0 < ε) :
    ∃ (X : ℕ) (hX : 0 < X), 3 / 4 < (gadget X hX).polyDensity ∧
      (gadget X hX).polyDensity < 3 / 4 + ε ∧ ¬ (gadget X hX).Schedulable := by
  obtain ⟨X, hXε⟩ := exists_nat_gt (1 / ε)
  have hX : 0 < X := by
    have : (0 : ℝ) < 1 / ε := by positivity
    exact_mod_cast this.trans hXε
  have hXr : (0 : ℝ) < X := by exact_mod_cast hX
  refine ⟨X, hX, ?_, ?_, gadget_infeasible X hX⟩
  · rw [gadget_polyDensity]; have : (0 : ℝ) < 1 / X := by positivity
    linarith
  · rw [gadget_polyDensity]
    have : 1 / (X : ℝ) < ε := by
      rw [div_lt_iff₀ hXr]; rw [div_lt_iff₀ hε] at hXε; linarith
    linarith

#print axioms poly_density_question_false
#print axioms infeasible_below

end PolySched
