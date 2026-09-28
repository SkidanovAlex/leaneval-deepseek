import Mathlib
import Submission.Work.HP.GonLib
import Submission.Work.HP.LatRecurseDefs
import Submission.Work.HP.lat_min_attained
import Submission.Work.HP.LatRecurse.ncard_fiber_le
import Submission.Work.HP.LatRecurse.ncard_int_interval
import Submission.Work.HP.LatRecurse.linearIndependent_int_rat
import Submission.Work.HP.Sig2.primBasisExt
import Submission.Work.HP.Sig2.projPerpFacts

/-!
# The Schmidt recursion for lattice points in a ball (`Work.HP.Sig2Rec`)

This file assembles the one-step recursion used in the proof of Schmidt's bound

`#(L ∩ B(T)) ≤ K · ∏_{i ≤ rk L} (T / λ_i(L) + 1)`

for a lattice `L ⊆ ℤ^ι`, together with the rank induction that turns it into the product bound
(in coefficient space, for a presentation `Φ : ℝ^R → E`).

The recursion (`recursion`) peels off a shortest vector `u` of the presented lattice and projects
orthogonally onto `u^⊥`.  Its proof body (the integer/real coefficient maps `sigmaZ`, `sigmaR`,
`TZ`, the finiteness of the coefficient ball, the fibre count and the comparison
`λ_{j+1}/2 ≤ μ_j` of successive minima) is taken from the team's file
`Submission/Work/HP/lat_recurse.lean`, where the five local placeholders `_P1`–`_P6` were supplied
by the lemmas below; `_P4`, `_P5`, `_P6` are `Submission.Work.HP.LatRecurse.ncard_fiber_le`,
`ncard_int_interval` and `linearIndependent_int_rat`.  The two structural inputs are
* `primBasis_of_prim`: a primitive vector extends to a `ℤ`-basis, and
* `projPerp_facts`: the elementary facts about the orthogonal projection.
These are proved in `Submission.Work.HP.Sig2.primBasisExt` and
`Submission.Work.HP.Sig2.projPerpFacts` respectively, and re-exported here under the names used
below.  The remaining ingredients (`ncard_fiber_le`, `ncard_int_interval`,
`linearIndependent_int_rat`) are the team's lemmas in `Submission.Work.HP.LatRecurse`.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.HP.Sig2Rec

open Finset

/-! ## The two structural inputs (proved in neighbouring files) -/

/-- A primitive vector extends to a `ℤ`-basis of `Fin R → ℤ` whose realification is `ℝ`-linearly
independent. -/
theorem primBasis_of_prim {R : ℕ} (hR : 1 ≤ R) (u : Fin R → ℤ) (hu : Work.HP.IsPrim u) :
    ∃ v : Fin (R - 1) → (Fin R → ℤ),
      Function.Bijective (fun c : ℤ × (Fin (R - 1) → ℤ) => c.1 • u + ∑ i, c.2 i • v i) ∧
      (∀ c : ℝ × (Fin (R - 1) → ℝ), c.1 • (fun j => (u j : ℝ)) +
        ∑ i, c.2 i • (fun j => ((v i) j : ℝ)) = 0 → c = 0) :=
  Work.HP.Sig2.primBasisExt hR u hu

/-- The elementary facts about the orthogonal projection `Work.HP.projPerp x` onto `(ℝ x)^⊥`. -/
theorem projPerp_facts {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (x y : E) :
    Work.HP.projPerp x y = y - (‖x‖ ^ 2)⁻¹ • (inner ℝ x y • x) ∧
    Work.HP.projPerp x x = 0 ∧
    inner ℝ x (Work.HP.projPerp x y) = 0 ∧
    ‖Work.HP.projPerp x y‖ ≤ ‖y‖ ∧
    (Work.HP.projPerp x y = 0 ↔ ∃ c : ℝ, y = c • x) ∧
    y = ((‖x‖ ^ 2)⁻¹ * inner ℝ x y) • x + Work.HP.projPerp x y :=
  Work.HP.Sig2.projPerpFacts x y

/-! ## The integer and real sections attached to a family of integer vectors -/

/-- `w ↦ ∑ i, w i • v i` as a `ℤ`-linear map. -/
def sigmaZ {R : ℕ} (v : Fin (R - 1) → (Fin R → ℤ)) :
    (Fin (R - 1) → ℤ) →ₗ[ℤ] (Fin R → ℤ) where
  toFun w := fun j => ∑ i, w i * v i j
  map_add' w w' := by
    funext j
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c w := by
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum, RingHom.id_apply]

lemma sigmaZ_apply {R : ℕ} (v : Fin (R - 1) → (Fin R → ℤ))
    (w : Fin (R - 1) → ℤ) (j : Fin R) : sigmaZ v w j = ∑ i, w i * v i j := rfl

lemma sigmaZ_eq_sum {R : ℕ} (v : Fin (R - 1) → (Fin R → ℤ)) (w : Fin (R - 1) → ℤ) :
    sigmaZ v w = ∑ i, w i • v i := by
  funext j
  simp only [sigmaZ_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- `w ↦ ∑ i, w i • v i` as an `ℝ`-linear map. -/
def sigmaR {R : ℕ} (v : Fin (R - 1) → (Fin R → ℤ)) :
    (Fin (R - 1) → ℝ) →ₗ[ℝ] (Fin R → ℝ) where
  toFun w := fun j => ∑ i, w i * (v i j : ℝ)
  map_add' w w' := by
    funext j
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c w := by
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum, RingHom.id_apply]

lemma sigmaR_apply {R : ℕ} (v : Fin (R - 1) → (Fin R → ℤ))
    (w : Fin (R - 1) → ℝ) (j : Fin R) : sigmaR v w j = ∑ i, w i * (v i j : ℝ) := rfl

lemma sigmaR_eq_sum {R : ℕ} (v : Fin (R - 1) → (Fin R → ℤ)) (w : Fin (R - 1) → ℝ) :
    sigmaR v w = ∑ i, w i • (fun j => (v i j : ℝ)) := by
  funext j
  simp only [sigmaR_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

lemma sigmaR_cast {R : ℕ} (v : Fin (R - 1) → (Fin R → ℤ)) (w : Fin (R - 1) → ℤ) :
    (fun j => ((sigmaZ v w) j : ℝ)) = sigmaR v (fun i => (w i : ℝ)) := by
  funext j
  simp only [sigmaZ_apply, sigmaR_apply, Int.cast_sum, Int.cast_mul]

lemma cast_smul_add {R : ℕ} (u : Fin R → ℤ) (v : Fin (R - 1) → (Fin R → ℤ)) (a : ℤ)
    (w : Fin (R - 1) → ℤ) :
    (fun j => ((a • u + sigmaZ v w) j : ℝ)) =
      (a : ℝ) • (fun j => (u j : ℝ)) + sigmaR v (fun i => (w i : ℝ)) := by
  funext j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sigmaZ_apply, sigmaR_apply]
  push_cast
  ring

lemma cast_sub_smul {R : ℕ} (u : Fin R → ℤ) (z : Fin R → ℤ) (m : ℤ) :
    (fun j => ((z - m • u) j : ℝ)) =
      (fun j => (z j : ℝ)) - (m : ℝ) • (fun j => (u j : ℝ)) := by
  funext j
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

/-- The `ℤ`-linear decomposition map `(a, w) ↦ a • u + ∑ i, w i • v i`. -/
def TZ {R : ℕ} (u : Fin R → ℤ) (v : Fin (R - 1) → (Fin R → ℤ)) :
    (ℤ × (Fin (R - 1) → ℤ)) →ₗ[ℤ] (Fin R → ℤ) :=
  (LinearMap.toSpanSingleton ℤ (Fin R → ℤ) u).comp (LinearMap.fst ℤ ℤ (Fin (R - 1) → ℤ)) +
    (sigmaZ v).comp (LinearMap.snd ℤ ℤ (Fin (R - 1) → ℤ))

lemma TZ_apply {R : ℕ} (u : Fin R → ℤ) (v : Fin (R - 1) → (Fin R → ℤ))
    (a : ℤ) (w : Fin (R - 1) → ℤ) : TZ u v (a, w) = a • u + sigmaZ v w := by
  simp [TZ, LinearMap.toSpanSingleton_apply]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The set of coefficient vectors of lattice points of norm `≤ T` is finite. -/
lemma latSet_finite_aux {R : ℕ} (Φ : LatMap (ι := ι) R) (hΦ : Function.Injective Φ) (T : ℝ) :
    (latSet Φ T).Finite := by
  classical
  obtain ⟨K, -, hK⟩ := Φ.exists_antilipschitzWith (LinearMap.ker_eq_bot.mpr hΦ)
  refine (Set.Finite.pi fun _ : Fin R => Set.finite_Icc (-⌈(K : ℝ) * T⌉) ⌈(K : ℝ) * T⌉).subset ?_
  intro t ht
  rw [Set.mem_pi]
  intro i _
  rw [Set.mem_Icc]
  have hb : |(t i : ℝ)| ≤ (K : ℝ) * T := by
    have h1 : ‖(t i : ℝ)‖ ≤ ‖fun j : Fin R => (t j : ℝ)‖ :=
      norm_le_pi_norm (fun j : Fin R => (t j : ℝ)) i
    have h2 : ‖fun j : Fin R => (t j : ℝ)‖ ≤ (K : ℝ) * ‖Φ (fun j : Fin R => (t j : ℝ))‖ := by
      have := hK.le_mul_dist (fun j : Fin R => (t j : ℝ)) 0
      simpa [dist_zero_right, map_zero] using this
    calc |(t i : ℝ)| = ‖(t i : ℝ)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fun j : Fin R => (t j : ℝ)‖ := h1
      _ ≤ (K : ℝ) * ‖Φ (fun j : Fin R => (t j : ℝ))‖ := h2
      _ ≤ (K : ℝ) * T := mul_le_mul_of_nonneg_left ht K.coe_nonneg
  obtain ⟨hlo, hhi⟩ := abs_le.mp hb
  constructor
  · have hcast : ((-⌈(K : ℝ) * T⌉ : ℤ) : ℝ) ≤ ((t i : ℤ) : ℝ) := by
      push_cast
      calc -(⌈(K : ℝ) * T⌉ : ℝ) ≤ -((K : ℝ) * T) := neg_le_neg (Int.le_ceil _)
        _ ≤ (t i : ℝ) := hlo
    exact Int.cast_le.mp hcast
  · have hcast : ((t i : ℤ) : ℝ) ≤ ((⌈(K : ℝ) * T⌉ : ℤ) : ℝ) := hhi.trans (Int.le_ceil _)
    exact Int.cast_le.mp hcast

/-- There are no `ℤ`-linearly independent families of `m > R` vectors in `ℤ^R`. -/
lemma not_linind_int_of_lt {R m : ℕ} (h : R < m) (f : Fin m → (Fin R → ℤ)) :
    ¬ LinearIndependent ℤ f := by
  intro hf
  have hf' : LinearIndependent ℚ (fun i => (fun j => ((f i) j : ℚ))) :=
    (Work.HP.LatRecurse.linearIndependent_int_rat (R := R) (m := m) (f := f)).mp hf
  have hle := hf'.fintype_card_le_finrank
  rw [Fintype.card_fin, Module.finrank_fin_fun] at hle
  omega

/-- For a nonzero coefficient vector `w` the projected lattice vector has norm at least half of the
shortest lattice vector. -/
lemma half_le_norm_aux {R : ℕ} (Φ : LatMap (ι := ι) R) (hΦ : Function.Injective Φ)
    {u : Fin R → ℤ} {v : Fin (R - 1) → (Fin R → ℤ)}
    (hTbij : Function.Bijective (TZ u v))
    {x0 : EuclideanSpace ℝ ι} (hx0 : x0 = Φ (fun i => (u i : ℝ)))
    (hmin : ∀ y : Fin R → ℤ, y ≠ 0 → ‖x0‖ ≤ ‖Φ (fun i => (y i : ℝ))‖)
    (w : Fin (R - 1) → ℤ) (hw : w ≠ 0) :
    ‖x0‖ / 2 ≤ ‖projPerp x0 (Φ (sigmaR v (fun i => (w i : ℝ))))‖ := by
  classical
  have hz : sigmaZ v w ≠ 0 := by
    intro h
    have h1 : TZ u v (0, w) = TZ u v (0, 0) := by
      simp [TZ_apply, h]
    have h2 := hTbij.1 h1
    exact hw (by simpa using congrArg Prod.snd h2)
  set c : ℝ := (‖x0‖ ^ 2)⁻¹ * inner ℝ x0 (Φ (sigmaR v (fun i => (w i : ℝ)))) with hc
  set m : ℤ := ⌊c + 1 / 2⌋ with hm
  have hsplit : Φ (sigmaR v (fun i => (w i : ℝ))) =
      c • x0 + projPerp x0 (Φ (sigmaR v (fun i => (w i : ℝ)))) :=
    (projPerp_facts x0 (Φ (sigmaR v (fun i => (w i : ℝ))))).2.2.2.2.2
  have hyne : sigmaZ v w - m • u ≠ 0 := by
    intro h
    have h1 : sigmaZ v w = m • u := sub_eq_zero.mp h
    have h2 : TZ u v (-m, w) = TZ u v (0, 0) := by
      simp [TZ_apply, h1]
    have h3 := hTbij.1 h2
    exact hw (by simpa using congrArg Prod.snd h3)
  have hmin' := hmin (sigmaZ v w - m • u) hyne
  have hcast2 : (fun j => ((sigmaZ v w - m • u) j : ℝ)) =
      sigmaR v (fun i => (w i : ℝ)) - (m : ℝ) • (fun j => (u j : ℝ)) := by
    rw [cast_sub_smul, sigmaR_cast]
  have hΦy : Φ (fun j => ((sigmaZ v w - m • u) j : ℝ)) =
      (c - m) • x0 + projPerp x0 (Φ (sigmaR v (fun i => (w i : ℝ)))) := by
    have step : Φ (fun j => ((sigmaZ v w - m • u) j : ℝ)) =
        Φ (sigmaR v (fun i => (w i : ℝ))) - (m : ℝ) • x0 := by
      rw [hcast2, map_sub, map_smul, ← hx0]
    rw [step]
    conv_lhs => rw [hsplit]
    module
  have hm_close : |c - (m : ℝ)| ≤ 1 / 2 := by
    have h1 : (m : ℝ) ≤ c + 1 / 2 := by
      rw [hm]; exact Int.floor_le (c + 1 / 2)
    have h2 : c + 1 / 2 < (m : ℝ) + 1 := by
      rw [hm]; exact Int.lt_floor_add_one (c + 1 / 2)
    rw [abs_le]
    constructor <;> linarith
  have htri : ‖(c - m) • x0 + projPerp x0 (Φ (sigmaR v (fun i => (w i : ℝ))))‖ ≤
      |c - (m : ℝ)| * ‖x0‖ + ‖projPerp x0 (Φ (sigmaR v (fun i => (w i : ℝ))))‖ := by
    calc ‖(c - m) • x0 + projPerp x0 (Φ (sigmaR v (fun i => (w i : ℝ))))‖
        ≤ ‖(c - m) • x0‖ + ‖projPerp x0 (Φ (sigmaR v (fun i => (w i : ℝ))))‖ := norm_add_le _ _
      _ = |c - (m : ℝ)| * ‖x0‖ + ‖projPerp x0 (Φ (sigmaR v (fun i => (w i : ℝ))))‖ := by
            rw [norm_smul, Real.norm_eq_abs]
  have hle : ‖x0‖ ≤ |c - (m : ℝ)| * ‖x0‖ + ‖projPerp x0 (Φ (sigmaR v (fun i => (w i : ℝ))))‖ := by
    rw [hΦy] at hmin'
    exact hmin'.trans htri
  have h2 : |c - (m : ℝ)| * ‖x0‖ ≤ (1 / 2) * ‖x0‖ :=
    mul_le_mul_of_nonneg_right hm_close (norm_nonneg _)
  linarith

/-! ## The main theorem -/

theorem recursion {ι : Type*} [Fintype ι] [DecidableEq ι] {R : ℕ} (hR : 1 ≤ R)
    (Φ : LatMap (ι := ι) R) (hΦ : Function.Injective Φ)
    (u : Fin R → ℤ) (hu0 : u ≠ 0) (hup : IsPrim u)
    (hu : ‖Φ (fun i => (u i : ℝ))‖ = latMin Φ 1) :
    ∃ Ψ : LatMap (ι := ι) (R - 1), Function.Injective Ψ ∧
      (∀ T : ℝ, 0 ≤ T → (latCount Φ T : ℝ) ≤
        (2 * T / ‖Φ (fun i => (u i : ℝ))‖ + 1) * (latCount Ψ T : ℝ)) ∧
      (∀ j : ℕ, 1 ≤ j → latMin Φ (j + 1) / 2 ≤ latMin Ψ j) := by
  classical
  obtain ⟨v, hvbij, hvinj⟩ := primBasis_of_prim hR u hup
  have hTbij : Function.Bijective (TZ u v) := by
    have hfun : TZ u v = fun c : ℤ × (Fin (R - 1) → ℤ) =>
        c.1 • u + ∑ i, c.2 i • v i := by
      funext c
      rw [TZ_apply, sigmaZ_eq_sum]
    rw [hfun]
    exact hvbij
  set x0 : EuclideanSpace ℝ ι := Φ (fun i => (u i : ℝ)) with hx0def
  have huR0 : (fun i => (u i : ℝ)) ≠ 0 := by
    intro h
    refine hu0 (funext fun i => ?_)
    have hi : ((u i : ℤ) : ℝ) = 0 := by simpa using congrFun h i
    simpa using Int.cast_eq_zero.mp hi
  have hx0ne : x0 ≠ 0 := by
    intro h
    have h1 : Φ (fun i => (u i : ℝ)) = 0 := by rw [← hx0def]; exact h
    exact huR0 (hΦ (by rw [h1, map_zero]))
  have hx0pos : 0 < ‖x0‖ := norm_pos_iff.mpr hx0ne
  have hmin : ∀ y : Fin R → ℤ, y ≠ 0 → ‖x0‖ ≤ ‖Φ (fun i => (y i : ℝ))‖ := by
    intro y hy
    have hmem : ‖Φ (fun i => (y i : ℝ))‖ ∈ {r : ℝ | 0 ≤ r ∧ ∃ f : Fin 1 → (Fin R → ℤ),
        LinearIndependent ℤ f ∧ ∀ i, ‖Φ (fun k => (f i k : ℝ))‖ ≤ r} := by
      refine ⟨norm_nonneg _, fun _ => y, ?_, fun _ => le_rfl⟩
      rw [linearIndependent_unique_iff]
      exact hy
    have hbdd : BddBelow {r : ℝ | 0 ≤ r ∧ ∃ f : Fin 1 → (Fin R → ℤ),
        LinearIndependent ℤ f ∧ ∀ i, ‖Φ (fun k => (f i k : ℝ))‖ ≤ r} :=
      ⟨0, fun r hr => hr.1⟩
    calc ‖x0‖ = ‖Φ (fun i => (u i : ℝ))‖ := by rw [hx0def]
      _ = latMin Φ 1 := hu
      _ ≤ ‖Φ (fun i => (y i : ℝ))‖ := csInf_le hbdd hmem
  set Ψ : LatMap (ι := ι) (R - 1) := (projPerp x0).comp (Φ.comp (sigmaR v)) with hΨdef
  have hΨinj : Function.Injective Ψ := by
    intro w w' hww'
    have h0 : projPerp x0 (Φ (sigmaR v (w - w'))) = 0 := by
      have h1 : Ψ (w - w') = 0 := by rw [map_sub, hww', sub_self]
      simpa [hΨdef, LinearMap.comp_apply] using h1
    obtain ⟨c, hc⟩ := (projPerp_facts x0 (Φ (sigmaR v (w - w')))).2.2.2.2.1.mp h0
    have hcs : sigmaR v (w - w') = c • (fun j => (u j : ℝ)) := by
      apply hΦ
      rw [hc, map_smul, ← hx0def]
    have hzero : (-c) • (fun j => (u j : ℝ)) +
        ∑ i, (w - w') i • (fun j => (v i j : ℝ)) = 0 := by
      rw [← sigmaR_eq_sum v (w - w'), hcs, neg_smul, neg_add_cancel]
    have hres := hvinj (-c, w - w') hzero
    have h2 : w - w' = 0 := by
      have h3 := congrArg Prod.snd hres
      simpa using h3
    exact sub_eq_zero.mp h2
  refine ⟨Ψ, hΨinj, ?_, ?_⟩
  · intro T hT
    let e : (ℤ × (Fin (R - 1) → ℤ)) ≃ (Fin R → ℤ) :=
      Equiv.ofBijective (fun c : ℤ × (Fin (R - 1) → ℤ) => c.1 • u + ∑ i, c.2 i • v i) hvbij
    have hep : ∀ p : ℤ × (Fin (R - 1) → ℤ), e p = p.1 • u + sigmaZ v p.2 := by
      intro p
      rw [Equiv.ofBijective_apply, sigmaZ_eq_sum]
    have hes : ∀ y : Fin R → ℤ, y = (e.symm y).1 • u + sigmaZ v (e.symm y).2 := by
      intro y
      conv_lhs => rw [← Equiv.apply_symm_apply e y]
      rw [hep]
    have hdecR : ∀ y : Fin R → ℤ,
        (fun j => (y j : ℝ)) =
          ((e.symm y).1 : ℝ) • (fun j => (u j : ℝ)) +
            sigmaR v (fun i => ((e.symm y).2 i : ℝ)) := by
      intro y
      conv_lhs => rw [hes y]
      rw [cast_smul_add]
    set cc : (Fin (R - 1) → ℤ) → ℝ := fun w =>
      (‖x0‖ ^ 2)⁻¹ * inner ℝ x0 (Φ (sigmaR v (fun i => (w i : ℝ)))) with hcc
    have hkey : ∀ y : Fin R → ℤ,
        Φ (fun j => (y j : ℝ)) =
          ((e.symm y).1 + cc (e.symm y).2) • x0 +
            projPerp x0 (Φ (sigmaR v (fun i => ((e.symm y).2 i : ℝ)))) := by
      intro y
      have h1 : Φ (fun j => (y j : ℝ)) =
          ((e.symm y).1 : ℝ) • x0 + Φ (sigmaR v (fun i => ((e.symm y).2 i : ℝ))) := by
        conv_lhs => rw [hdecR y]
        rw [map_add, map_smul, ← hx0def]
      have h2 : Φ (sigmaR v (fun i => ((e.symm y).2 i : ℝ))) =
          cc (e.symm y).2 • x0 +
            projPerp x0 (Φ (sigmaR v (fun i => ((e.symm y).2 i : ℝ)))) :=
        (projPerp_facts x0 (Φ (sigmaR v (fun i => ((e.symm y).2 i : ℝ))))).2.2.2.2.2
      rw [h1]
      conv_lhs => rw [h2]
      rw [add_smul]
      abel
    have hnorm : ∀ y : Fin R → ℤ,
        ‖Φ (fun j => (y j : ℝ))‖ ^ 2 =
          ((e.symm y).1 + cc (e.symm y).2) ^ 2 * ‖x0‖ ^ 2 +
            ‖projPerp x0 (Φ (sigmaR v (fun i => ((e.symm y).2 i : ℝ))))‖ ^ 2 := by
      intro y
      have horth : inner ℝ (((e.symm y).1 + cc (e.symm y).2) • x0)
          (projPerp x0 (Φ (sigmaR v (fun i => ((e.symm y).2 i : ℝ))))) = 0 := by
        rw [inner_smul_left, (projPerp_facts x0 (Φ (sigmaR v (fun i => ((e.symm y).2 i : ℝ))))).2.2.1]
        simp
      have hsq : ‖((e.symm y).1 + cc (e.symm y).2) • x0‖ ^ 2 =
          ((e.symm y).1 + cc (e.symm y).2) ^ 2 * ‖x0‖ ^ 2 := by
        rw [norm_smul]
        simp only [Real.norm_eq_abs, mul_pow, sq_abs]
      have hpp : ‖((e.symm y).1 + cc (e.symm y).2) • x0 +
            projPerp x0 (Φ (sigmaR v (fun i => ((e.symm y).2 i : ℝ))))‖ ^ 2 =
          ‖((e.symm y).1 + cc (e.symm y).2) • x0‖ ^ 2 +
            ‖projPerp x0 (Φ (sigmaR v (fun i => ((e.symm y).2 i : ℝ))))‖ ^ 2 := by
        have h := norm_add_sq_eq_norm_sq_add_norm_sq_real
          (x := ((e.symm y).1 + cc (e.symm y).2) • x0)
          (y := projPerp x0 (Φ (sigmaR v (fun i => ((e.symm y).2 i : ℝ))))) horth
        simpa only [sq] using h
      rw [hkey y, hpp, hsq]
    have hle1 : ∀ y : Fin R → ℤ,
        ‖projPerp x0 (Φ (sigmaR v (fun i => ((e.symm y).2 i : ℝ))))‖ ≤
          ‖Φ (fun j => (y j : ℝ))‖ := by
      intro y
      have h2 : ‖projPerp x0 (Φ (sigmaR v (fun i => ((e.symm y).2 i : ℝ))))‖ ^ 2 ≤
          ‖Φ (fun j => (y j : ℝ))‖ ^ 2 := by
        rw [hnorm y]
        nlinarith [sq_nonneg (((e.symm y).1 + cc (e.symm y).2) * ‖x0‖)]
      simpa only [abs_of_nonneg (norm_nonneg _)] using sq_le_sq.mp h2
    have hle2 : ∀ y : Fin R → ℤ,
        |((e.symm y).1 : ℝ) + cc (e.symm y).2| * ‖x0‖ ≤ ‖Φ (fun j => (y j : ℝ))‖ := by
      intro y
      have h2 : (((e.symm y).1 : ℝ) + cc (e.symm y).2) ^ 2 * ‖x0‖ ^ 2 ≤
          ‖Φ (fun j => (y j : ℝ))‖ ^ 2 := by
        rw [hnorm y]
        nlinarith [sq_nonneg ‖projPerp x0 (Φ (sigmaR v (fun i => ((e.symm y).2 i : ℝ))))‖]
      have h3 : (((e.symm y).1 : ℝ) + cc (e.symm y).2) ^ 2 * ‖x0‖ ^ 2 =
          (|((e.symm y).1 : ℝ) + cc (e.symm y).2| * ‖x0‖) ^ 2 := by
        rw [mul_pow, sq_abs]
      rw [h3] at h2
      simpa only [abs_of_nonneg (mul_nonneg (abs_nonneg _) (norm_nonneg _)),
        abs_of_nonneg (norm_nonneg _)] using sq_le_sq.mp h2
    set K : ℕ := Nat.floor (2 * (T / ‖x0‖)) + 1 with hKdef
    have hKle : (K : ℝ) ≤ 2 * T / ‖x0‖ + 1 := by
      have h0 : (0 : ℝ) ≤ 2 * (T / ‖x0‖) := by positivity
      have h1 : ((Nat.floor (2 * (T / ‖x0‖)) : ℕ) : ℝ) ≤ 2 * (T / ‖x0‖) := Nat.floor_le h0
      have h2 : 2 * (T / ‖x0‖) = 2 * T / ‖x0‖ := by ring
      simp only [hKdef]
      push_cast
      linarith
    set S : Set (ℤ × (Fin (R - 1) → ℤ)) := {p | ‖Φ (fun j => ((e p) j : ℝ))‖ ≤ T} with hSdef
    have hfiber : ∀ w : Fin (R - 1) → ℤ, {a : ℤ | (a, w) ∈ S}.ncard ≤ K := by
      intro w
      have hsub : {a : ℤ | (a, w) ∈ S} ⊆ {a : ℤ | |(a : ℝ) + cc w| ≤ T / ‖x0‖} := by
        intro a ha
        show |(a : ℝ) + cc w| ≤ T / ‖x0‖
        have ha' : ‖Φ (fun j => ((e (a, w)) j : ℝ))‖ ≤ T := ha
        have h2 := hle2 (e (a, w))
        rw [Equiv.symm_apply_apply e (a, w)] at h2
        have h3 : |(a : ℝ) + cc w| * ‖x0‖ ≤ T := le_trans h2 ha'
        rw [le_div_iff₀ hx0pos]
        exact h3
      have hfin : ({a : ℤ | |(a : ℝ) + cc w| ≤ T / ‖x0‖} : Set ℤ).Finite := by
        refine Set.Finite.subset
          (Set.finite_Icc (Int.floor (-(T / ‖x0‖) - cc w)) (Int.ceil (T / ‖x0‖ - cc w))) ?_
        intro a ha
        have h : |(a : ℝ) + cc w| ≤ T / ‖x0‖ := ha
        have h := abs_le.mp h
        refine ⟨?_, ?_⟩
        · refine Int.cast_le.mp (show ((Int.floor (-(T / ‖x0‖) - cc w) : ℤ) : ℝ) ≤ ((a : ℤ) : ℝ) from ?_)
          have h3 : ((Int.floor (-(T / ‖x0‖) - cc w) : ℤ) : ℝ) ≤ -(T / ‖x0‖) - cc w :=
            Int.floor_le (-(T / ‖x0‖) - cc w)
          linarith [h.1]
        · refine Int.cast_le.mp (show ((a : ℤ) : ℝ) ≤ ((Int.ceil (T / ‖x0‖ - cc w) : ℤ) : ℝ) from ?_)
          have h3 : T / ‖x0‖ - cc w ≤ ((Int.ceil (T / ‖x0‖ - cc w) : ℤ) : ℝ) :=
            Int.le_ceil (T / ‖x0‖ - cc w)
          linarith [h.2]
      refine le_trans (Set.ncard_le_ncard hsub hfin)
        (Work.HP.LatRecurse.ncard_int_interval (c := cc w) (M := T / ‖x0‖) (by positivity))
    have hcard2 : S.ncard ≤ K * (S.image Prod.snd).ncard := Work.HP.LatRecurse.ncard_fiber_le S K hfiber
    have hcard1 : (latSet Φ T).ncard = S.ncard := by
      have himg : e '' S = latSet Φ T := by
        ext y
        constructor
        · rintro ⟨p, hp, rfl⟩
          exact hp
        · intro hy
          refine ⟨e.symm y, ?_, Equiv.apply_symm_apply e y⟩
          show ‖Φ (fun j => ((e (e.symm y)) j : ℝ))‖ ≤ T
          rw [Equiv.apply_symm_apply e y]
          exact hy
      rw [← himg, Set.ncard_image_of_injective S e.injective]
    have hcard3 : (S.image Prod.snd).ncard ≤ (latSet Ψ T).ncard := by
      refine Set.ncard_le_ncard ?_ (latSet_finite_aux Ψ hΨinj T)
      rintro w ⟨p, hp, rfl⟩
      have h := hle1 (e p)
      rw [Equiv.symm_apply_apply e p] at h
      exact le_trans (by simpa [hΨdef, LinearMap.comp_apply] using h) hp
    rw [latCount, latCount, hcard1]
    calc (S.ncard : ℝ) ≤ (K : ℝ) * ((S.image Prod.snd).ncard : ℝ) := by exact_mod_cast hcard2
      _ ≤ (K : ℝ) * ((latSet Ψ T).ncard : ℝ) :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast hcard3) (Nat.cast_nonneg K)
      _ ≤ (2 * T / ‖x0‖ + 1) * ((latSet Ψ T).ncard : ℝ) :=
          mul_le_mul_of_nonneg_right hKle (Nat.cast_nonneg _)
      _ = (2 * T / ‖Φ (fun i => (u i : ℝ))‖ + 1) * ((latSet Ψ T).ncard : ℝ) := by
          rw [hx0def]
  · intro j hj
    set A : Set ℝ := {r : ℝ | 0 ≤ r ∧ ∃ f : Fin (j + 1) → (Fin R → ℤ),
        LinearIndependent ℤ f ∧ ∀ i, ‖Φ (fun k => (f i k : ℝ))‖ ≤ r} with hA
    set B : Set ℝ := {r : ℝ | 0 ≤ r ∧ ∃ g : Fin j → (Fin (R - 1) → ℤ),
        LinearIndependent ℤ g ∧ ∀ i, ‖Ψ (fun k => (g i k : ℝ))‖ ≤ r} with hB
    have hBddA : BddBelow A := ⟨0, fun r hr => hr.1⟩
    have hBddB : BddBelow B := ⟨0, fun r hr => hr.1⟩
    rcases lt_or_ge R (j + 1) with hlt | hge
    · have hAe : A = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro r ⟨-, f, hf, -⟩
        exact not_linind_int_of_lt hlt f hf
      have hBe : B = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro r ⟨-, g, hg, -⟩
        exact not_linind_int_of_lt (R := R - 1) (by omega) g hg
      change sInf A / 2 ≤ sInf B
      rw [hAe, hBe, Real.sInf_empty]
      norm_num
    · have hjR : j ≤ R - 1 := by omega
      have hBne : B.Nonempty := by
        set g : Fin j → (Fin (R - 1) → ℤ) :=
          fun l => (Pi.basisFun ℤ (Fin (R - 1))) (Fin.castLE hjR l) with hg
        have hgLI : LinearIndependent ℤ g := by
          have hb : LinearIndependent ℤ ((Pi.basisFun ℤ (Fin (R - 1))) ∘ Fin.castLE hjR) :=
            (Pi.basisFun ℤ (Fin (R - 1))).linearIndependent.comp (Fin.castLE hjR)
              (Fin.castLE_injective hjR)
          show LinearIndependent ℤ ((Pi.basisFun ℤ (Fin (R - 1))) ∘ Fin.castLE hjR)
          exact hb
        refine ⟨∑ l, ‖Ψ (fun k => (g l k : ℝ))‖, ?_, ?_⟩
        · exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)
        · exact ⟨g, hgLI, fun l =>
            Finset.single_le_sum (fun k _ => norm_nonneg (Ψ (fun i => (g k i : ℝ))))
              (Finset.mem_univ l)⟩
      have hstep : ∀ r ∈ B, 2 * r ∈ A := by
        intro r hr
        obtain ⟨hr0, g, hgLI, hgr⟩ := hr
        have hg0 : g ⟨0, hj⟩ ≠ 0 := hgLI.ne_zero ⟨0, hj⟩
        have hhalf := half_le_norm_aux Φ hΦ hTbij hx0def hmin (g ⟨0, hj⟩) hg0
        have hr2 : ‖x0‖ / 2 ≤ r := le_trans hhalf (hgr ⟨0, hj⟩)
        set cf : Fin j → ℝ := fun l =>
          (‖x0‖ ^ 2)⁻¹ * inner ℝ x0 (Φ (sigmaR v (fun i => (g l i : ℝ)))) with hcf
        set mf : Fin j → ℤ := fun l => ⌊cf l + 1 / 2⌋ with hmf
        set F : Fin (j + 1) → (Fin R → ℤ) :=
          TZ u v ∘ Fin.cons (1, 0) (fun l => (-mf l, g l)) with hF
        have hF0 : F 0 = u := by
          rw [hF]
          simp [Function.comp_apply, Fin.cons_zero, TZ_apply]
        have hFsucc : ∀ l : Fin j, F l.succ = sigmaZ v (g l) - mf l • u := by
          intro l
          rw [hF]
          simp only [Function.comp_apply, Fin.cons_succ]
          rw [TZ_apply]
          module
        have hφLI : LinearIndependent ℤ (Fin.cons (1, 0) (fun l : Fin j => (-mf l, g l))) := by
          rw [Fintype.linearIndependent_iff]
          intro d hd
          have hd2 : ∑ l : Fin j, d l.succ • g l = 0 := by
            have h := congrArg Prod.snd hd
            simpa [Fin.sum_univ_succ, Prod.snd_sum, Prod.smul_snd] using h
          have hLI' : ∀ (c : Fin j → ℤ), (∑ l : Fin j, c l • g l = 0) → ∀ l, c l = 0 := by
            rw [Fintype.linearIndependent_iff] at hgLI
            exact hgLI
          have hcg : ∀ l : Fin j, d l.succ = 0 := hLI' _ hd2
          have hd0 : d 0 = 0 := by
            have h := congrArg Prod.fst hd
            have h3 : d 0 + ∑ l : Fin j, d l.succ * (-mf l) = 0 := by
              simpa [Fin.sum_univ_succ, Prod.fst_sum, Prod.smul_fst] using h
            have h4 : ∑ l : Fin j, d l.succ * (-mf l) = 0 := by
              have h5 : ∀ l : Fin j, d l.succ = 0 := hcg
              simp [h5]
            linarith
          intro i
          rcases Fin.eq_zero_or_eq_succ i with h | ⟨l, rfl⟩
          · rw [h]; exact hd0
          · exact hcg l
        have hFLI : LinearIndependent ℤ F := by
          rw [Fintype.linearIndependent_iff]
          intro d hd
          rw [Fintype.linearIndependent_iff] at hφLI
          refine hφLI d ?_
          apply hTbij.1
          rw [map_zero]
          have hd' : ∑ i : Fin (j + 1), d i • F i = 0 := hd
          simp only [hF, Function.comp_apply] at hd'
          rw [← hd']
          simp only [map_sum, map_smul]
        have hnormF : ∀ i : Fin (j + 1), ‖Φ (fun k => (F i k : ℝ))‖ ≤ 2 * r := by
          intro i
          rcases Fin.eq_zero_or_eq_succ i with h | ⟨l, rfl⟩
          · rw [h, hF0]
            have h1 : ‖Φ (fun k => (u k : ℝ))‖ = ‖x0‖ := by rw [hx0def]
            rw [h1]
            linarith
          · rw [hFsucc l]
            have hsplit : Φ (sigmaR v (fun i => (g l i : ℝ))) =
                cf l • x0 + Ψ (fun i => (g l i : ℝ)) := by
              conv_lhs => rw [(projPerp_facts x0 (Φ (sigmaR v (fun i => (g l i : ℝ))))).2.2.2.2.2]
              rfl
            have hcast3 : (fun k => ((sigmaZ v (g l) - mf l • u) k : ℝ)) =
                sigmaR v (fun i => (g l i : ℝ)) - (mf l : ℝ) • (fun k => (u k : ℝ)) :=
              by rw [cast_sub_smul, sigmaR_cast]
            have hclose : |(cf l - (mf l : ℝ))| ≤ 1 / 2 := by
              have h1 : (mf l : ℝ) ≤ cf l + 1 / 2 := by
                rw [hmf]; exact Int.floor_le (cf l + 1 / 2)
              have h2 : cf l + 1 / 2 < (mf l : ℝ) + 1 := by
                rw [hmf]; exact Int.lt_floor_add_one (cf l + 1 / 2)
              rw [abs_le]
              constructor <;> linarith
            have htri : ‖Φ (fun k => ((sigmaZ v (g l) - mf l • u) k : ℝ))‖ ≤
                |cf l - (mf l : ℝ)| * ‖x0‖ + ‖Ψ (fun i => (g l i : ℝ))‖ := by
              have e1 : Φ (fun k => ((sigmaZ v (g l) - mf l • u) k : ℝ)) =
                  cf l • x0 - (mf l : ℝ) • x0 + Ψ (fun i => (g l i : ℝ)) := by
                conv_lhs => rw [hcast3, map_sub, map_smul, hsplit, ← hx0def]
                module
              rw [e1]
              calc ‖cf l • x0 - (mf l : ℝ) • x0 + Ψ (fun i => (g l i : ℝ))‖
                  = ‖(cf l - (mf l : ℝ)) • x0 + Ψ (fun i => (g l i : ℝ))‖ := by
                    congr 1; module
                _ ≤ ‖(cf l - (mf l : ℝ)) • x0‖ + ‖Ψ (fun i => (g l i : ℝ))‖ := norm_add_le _ _
                _ = |cf l - (mf l : ℝ)| * ‖x0‖ + ‖Ψ (fun i => (g l i : ℝ))‖ := by
                    rw [norm_smul, Real.norm_eq_abs]
            have hb := hgr l
            have hmm : |cf l - (mf l : ℝ)| * ‖x0‖ ≤ (1 / 2) * ‖x0‖ :=
              mul_le_mul_of_nonneg_right hclose (norm_nonneg _)
            linarith
        exact ⟨by linarith, F, hFLI, hnormF⟩
      have hsInf : sInf A ≤ 2 * sInf B := by
        have h1 : sInf A / 2 ≤ sInf B := le_csInf hBne (fun r hr => by
          have h2 := csInf_le hBddA (hstep r hr)
          linarith)
        linarith
      change sInf A / 2 ≤ sInf B
      linarith
/-! ## Positivity and monotonicity of the successive minima in coefficient space -/

section LatMinBasics

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- If `j ≤ R` then the defining set of `latMin Φ j` is nonempty. -/
lemma latMin_set_nonempty {R : ℕ} (Φ : LatMap (ι := ι) R) {j : ℕ} (hj : j ≤ R) :
    ({r : ℝ | 0 ≤ r ∧ ∃ f : Fin j → (Fin R → ℤ), LinearIndependent ℤ f ∧
      ∀ k, ‖Φ (fun i => (f k i : ℝ))‖ ≤ r}).Nonempty := by
  set g : Fin j → ℝ := fun l => ‖Φ (fun i => (((Pi.basisFun ℤ (Fin R)) (Fin.castLE hj l)) i : ℝ))‖
  have hg : ∀ l, 0 ≤ g l := fun l => norm_nonneg _
  refine ⟨∑ l, g l, Finset.sum_nonneg (fun l _ => hg l),
    (fun k => (Pi.basisFun ℤ (Fin R)) (Fin.castLE hj k)), ?_, fun k => ?_⟩
  · exact LinearIndependent.comp (Pi.basisFun ℤ (Fin R)).linearIndependent
      (Fin.castLE hj) (Fin.castLE_injective hj)
  · exact Finset.single_le_sum (fun l _ => hg l) (Finset.mem_univ k)

lemma latMin_mono {R : ℕ} (Φ : LatMap (ι := ι) R) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ R) :
    latMin Φ i ≤ latMin Φ j := by
  rw [latMin, latMin]
  refine csInf_le_csInf (t := {r : ℝ | 0 ≤ r ∧ ∃ f : Fin i → (Fin R → ℤ), LinearIndependent ℤ f ∧
      ∀ k, ‖Φ (fun i => (f k i : ℝ))‖ ≤ r})
    ⟨0, fun r hr => hr.1⟩ (latMin_set_nonempty Φ hj) ?_
  rintro r ⟨hr0, f, hfind, hfr⟩
  exact ⟨hr0, fun k => f (Fin.castLE hij k),
    hfind.comp (Fin.castLE hij) (Fin.castLE_injective hij), fun k => hfr _⟩

lemma latMin_pos {R : ℕ} (Φ : LatMap (ι := ι) R) (hΦ : Function.Injective Φ) {j : ℕ}
    (h1 : 1 ≤ j) (hj : j ≤ R) : 0 < latMin Φ j := by
  obtain ⟨u, hu0, hup, hu⟩ := lat_min_attained (le_trans h1 hj) Φ hΦ
  have hpos1 : 0 < latMin Φ 1 := by
    rw [← hu, norm_pos_iff]
    intro h
    have h0 : (fun i => (u i : ℝ)) = 0 := hΦ (by rw [h, map_zero])
    exact hu0 (funext fun i => by
      have h2 : ((u i : ℤ) : ℝ) = 0 := congrFun h0 i
      exact_mod_cast h2)
  exact lt_of_lt_of_le hpos1 (latMin_mono Φ h1 hj)

/-- Elementary: `x/a + 1 ≤ 2 (x/b + 1)` when `0 ≤ x`, `a,b > 0` and `b/2 ≤ a`. -/
lemma div_add_one_le_two {x a b : ℝ} (hx : 0 ≤ x) (ha : 0 < a) (hb : 0 < b) (hab : b / 2 ≤ a) :
    x / a + 1 ≤ 2 * (x / b + 1) := by
  have h2 : x / a ≤ x / (b / 2) := div_le_div_of_nonneg_left hx (half_pos hb) hab
  have h3 : x / (b / 2) = 2 * (x / b) := by field_simp
  rw [h3] at h2
  linarith

end LatMinBasics

/-! ## The induction constant -/

/-- The constant of the induction on the rank: `Kcb 0 = 1`, `Kcb (n+1) = 2^{n+1} · Kcb n`. -/
def Kcb : ℕ → ℝ
  | 0 => 1
  | (n + 1) => 2 ^ (n + 1) * Kcb n

lemma Kcb_succ (n : ℕ) : Kcb (n + 1) = 2 ^ (n + 1) * Kcb n := rfl

lemma Kcb_pos : ∀ n, 0 < Kcb n := by
  intro n
  induction n with
  | zero => simp [Kcb]
  | succ n ih => rw [Kcb_succ]; positivity

lemma Kcb_nonneg (n : ℕ) : 0 ≤ Kcb n := (Kcb_pos n).le

lemma Kcb_le_succ (n : ℕ) : Kcb n ≤ Kcb (n + 1) := by
  rw [Kcb_succ]
  have h1 : (1 : ℝ) ≤ 2 ^ (n + 1) := one_le_pow₀ (by norm_num)
  nlinarith [Kcb_nonneg n]

lemma Kcb_mono : Monotone Kcb := by
  intro a b hab
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ m hm ih => exact ih.trans (Kcb_le_succ m)

/-! ## Schmidt's bound in coefficient space -/

/-- **Schmidt's bound in coefficient space.**  There is a constant `K = K(R) > 0` such that for
every injective presentation `Φ : ℝ^R → E` of a rank-`R` lattice and every `T ≥ 1`,

`#(Φ(ℤ^R) ∩ B(T)) ≤ K · ∏_{i=1}^{R} (T / λ_i(Φ) + 1)`.

The induction is on the rank: peel off a shortest vector `u` (`lat_min_attained`), use the
recursion `recursion` for the fibre count `#(Φ(ℤ^R) ∩ B(T)) ≤ (2T/‖Φ u‖ + 1) · #(Ψ(ℤ^{R-1}) ∩ B(T))`
and the comparison `λ_{j+1}(Φ)/2 ≤ λ_j(Ψ)` of successive minima, and absorb the two factors `2`. -/
theorem recursion_count :
    ∀ R : ℕ, ∀ (Φ : LatMap (ι := ι) R), Function.Injective Φ → ∀ T : ℝ, 1 ≤ T →
      (latCount Φ T : ℝ) ≤ Kcb R * ∏ i ∈ Finset.range R, (T / latMin Φ (i + 1) + 1) := by
  intro R
  induction R with
  | zero =>
      intro Φ hΦ T hT
      have hcard : latCount Φ T = 1 := by
        rw [latCount, latSet]
        have huniv : {t : Fin 0 → ℤ | ‖Φ (fun i => (t i : ℝ))‖ ≤ T} = Set.univ := by
          ext t
          simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
          have h0 : (fun i => (t i : ℝ)) = 0 := funext fun i => Fin.elim0 i
          rw [h0, map_zero, norm_zero]
          linarith
        rw [huniv, Set.ncard_univ, Nat.card_eq_fintype_card]
        simp
      rw [hcard]
      simp [Kcb]
  | succ n ih =>
      intro Φ hΦ T hT
      have hT0 : (0 : ℝ) ≤ T := by linarith
      have hR : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
      have hlampos : 0 < latMin Φ 1 := latMin_pos Φ hΦ le_rfl hR
      have hAnn : 0 ≤ 2 * T / latMin Φ 1 + 1 := by
        have : 0 ≤ 2 * T / latMin Φ 1 := div_nonneg (by linarith) hlampos.le
        linarith
      obtain ⟨u, hu_ne, hu_prim, hu_min⟩ := lat_min_attained hR Φ hΦ
      obtain ⟨Ψ, hΨinj, hcnt, hmin⟩ := recursion hR Φ hΦ u hu_ne hu_prim hu_min
      have hDmin : ∀ j, 1 ≤ j → latMin Φ (j + 1) / 2 ≤ latMin Ψ j := hmin
      have hcount : (latCount Φ T : ℝ) ≤ (2 * T / latMin Φ 1 + 1) * (latCount Ψ T : ℝ) := by
        have h1 := hcnt T hT0
        rw [hu_min] at h1
        exact h1
      have ihh : (latCount Ψ T : ℝ) ≤
          Kcb n * ∏ i ∈ Finset.range n, (T / latMin Ψ (i + 1) + 1) :=
        ih Ψ hΨinj T hT
      have hpt : ∀ i ∈ Finset.range n,
          T / latMin Ψ (i + 1) + 1 ≤ 2 * (T / latMin Φ (i + 2) + 1) := by
        intro i hi
        have hi' : i < n := Finset.mem_range.mp hi
        have ha : 0 < latMin Ψ (i + 1) :=
          latMin_pos Ψ hΨinj (by omega) (by omega)
        have hb : 0 < latMin Φ (i + 2) := latMin_pos Φ hΦ (by omega) (by omega)
        have hmin' : latMin Φ (i + 2) / 2 ≤ latMin Ψ (i + 1) := hDmin (i + 1) (by omega)
        exact div_add_one_le_two hT0 ha hb hmin'
      have hprod : ∏ i ∈ Finset.range n, (T / latMin Ψ (i + 1) + 1)
          ≤ 2 ^ n * ∏ i ∈ Finset.range n, (T / latMin Φ (i + 2) + 1) := by
        calc ∏ i ∈ Finset.range n, (T / latMin Ψ (i + 1) + 1)
            ≤ ∏ i ∈ Finset.range n, (2 * (T / latMin Φ (i + 2) + 1)) :=
              Finset.prod_le_prod₀ (fun i hi => by
                have hi' : i < n := Finset.mem_range.mp hi
                have hpos : 0 < latMin Ψ (i + 1) :=
                  latMin_pos Ψ hΨinj (by omega) (by omega)
                have : 0 ≤ T / latMin Ψ (i + 1) := div_nonneg hT0 hpos.le
                linarith) hpt
          _ = 2 ^ n * ∏ i ∈ Finset.range n, (T / latMin Φ (i + 2) + 1) := by
              rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
      have hsplit : ∏ i ∈ Finset.range (n + 1), (T / latMin Φ (i + 1) + 1)
          = (T / latMin Φ 1 + 1) * ∏ i ∈ Finset.range n, (T / latMin Φ (i + 2) + 1) := by
        rw [Finset.prod_range_succ', mul_comm]
      have hQnn : 0 ≤ ∏ i ∈ Finset.range n, (T / latMin Ψ (i + 1) + 1) :=
        Finset.prod_nonneg fun i hi => by
          have hi' : i < n := Finset.mem_range.mp hi
          have hpos : 0 < latMin Ψ (i + 1) := latMin_pos Ψ hΨinj (by omega) (by omega)
          have : 0 ≤ T / latMin Ψ (i + 1) := div_nonneg hT0 hpos.le
          linarith
      have hPnn : 0 ≤ ∏ i ∈ Finset.range n, (T / latMin Φ (i + 2) + 1) :=
        Finset.prod_nonneg fun i hi => by
          have hi' : i < n := Finset.mem_range.mp hi
          have hpos : 0 < latMin Φ (i + 2) := latMin_pos Φ hΦ (by omega) (by omega)
          have : 0 ≤ T / latMin Φ (i + 2) := div_nonneg hT0 hpos.le
          linarith
      have hA : 2 * T / latMin Φ 1 + 1 ≤ 2 * (T / latMin Φ 1 + 1) := by
        have : 2 * T / latMin Φ 1 = 2 * (T / latMin Φ 1) := by ring
        linarith
      have key : (2 * T / latMin Φ 1 + 1)
            * (Kcb n * ∏ i ∈ Finset.range n, (T / latMin Ψ (i + 1) + 1))
          ≤ Kcb (n + 1) * ∏ i ∈ Finset.range (n + 1), (T / latMin Φ (i + 1) + 1) := by
        rw [hsplit, Kcb_succ, pow_succ]
        have hfac : 0 ≤ Kcb n * 2 ^ n * ∏ i ∈ Finset.range n, (T / latMin Φ (i + 2) + 1) :=
          mul_nonneg (mul_nonneg (Kcb_nonneg n) (by positivity)) hPnn
        have h1 : (2 * T / latMin Φ 1 + 1)
              * (Kcb n * ∏ i ∈ Finset.range n, (T / latMin Ψ (i + 1) + 1))
            ≤ (2 * T / latMin Φ 1 + 1)
              * (Kcb n * (2 ^ n * ∏ i ∈ Finset.range n, (T / latMin Φ (i + 2) + 1))) := by
          refine mul_le_mul_of_nonneg_left ?_ hAnn
          exact mul_le_mul_of_nonneg_left hprod (Kcb_nonneg n)
        refine h1.trans ?_
        have h2 : (2 * T / latMin Φ 1 + 1)
              * (Kcb n * (2 ^ n * ∏ i ∈ Finset.range n, (T / latMin Φ (i + 2) + 1)))
            = (Kcb n * 2 ^ n * ∏ i ∈ Finset.range n, (T / latMin Φ (i + 2) + 1))
              * (2 * T / latMin Φ 1 + 1) := by ring
        rw [h2]
        have h3 : (Kcb n * 2 ^ n * ∏ i ∈ Finset.range n, (T / latMin Φ (i + 2) + 1))
              * (2 * T / latMin Φ 1 + 1)
            ≤ (Kcb n * 2 ^ n * ∏ i ∈ Finset.range n, (T / latMin Φ (i + 2) + 1))
              * (2 * (T / latMin Φ 1 + 1)) :=
          mul_le_mul_of_nonneg_left hA hfac
        refine h3.trans ?_
        exact le_of_eq (by ring)
      calc (latCount Φ T : ℝ)
          ≤ (2 * T / latMin Φ 1 + 1) * (latCount Ψ T : ℝ) := hcount
        _ ≤ (2 * T / latMin Φ 1 + 1)
              * (Kcb n * ∏ i ∈ Finset.range n, (T / latMin Ψ (i + 1) + 1)) :=
              mul_le_mul_of_nonneg_left ihh hAnn
        _ ≤ Kcb (n + 1) * ∏ i ∈ Finset.range (n + 1), (T / latMin Φ (i + 1) + 1) := key


/-! ## Transport between a sublattice `L ⊆ ℤ^ι` and its coefficient presentation

The following lemmas identify `ballCount` and the successive minima `lam` of a sublattice
`L ⊆ ℤ^ι` with `latCount` and `latMin` of the coefficient presentation `phiOf (vb b)` attached to
a `ℤ`-basis `b` of `L`. -/

section Transport

variable {L : Submodule ℤ (ι → ℤ)} {R : ℕ}

/-- The underlying integer vectors of a `ℤ`-basis of `L`. -/
def vb (b : Module.Basis (Fin R) ℤ L) (i : Fin R) : ι → ℤ := (b i : ι → ℤ)

/-- The `ℤ`-linear map `t ↦ Σ i, t i • b i` from coefficients to `ℤ^ι`. -/
noncomputable def latEmb (b : Module.Basis (Fin R) ℤ L) : (Fin R → ℤ) →ₗ[ℤ] (ι → ℤ) :=
  (Submodule.subtype L).comp b.equivFun.symm.toLinearMap

theorem latEmb_apply (b : Module.Basis (Fin R) ℤ L) (t : Fin R → ℤ) :
    latEmb b t = ∑ i, t i • vb b i := by
  show ((b.equivFun.symm t : L) : ι → ℤ) = _
  rw [Module.Basis.equivFun_symm_apply]
  exact (map_sum (Submodule.subtype L) (fun i => t i • b i) Finset.univ).trans
    (Finset.sum_congr rfl fun i _ => by rw [map_smul, vb, Submodule.coe_subtype])

theorem latEmb_equivFun (b : Module.Basis (Fin R) ℤ L) (x : L) :
    latEmb b (b.equivFun x) = (x : ι → ℤ) := by
  show ((b.equivFun.symm (b.equivFun x) : L) : ι → ℤ) = (x : ι → ℤ)
  rw [LinearEquiv.symm_apply_apply]

theorem latEmb_injective (b : Module.Basis (Fin R) ℤ L) : Function.Injective (latEmb b) := by
  intro x y h
  exact b.equivFun.symm.injective (Subtype.coe_injective h)

theorem latEmb_norm (b : Module.Basis (Fin R) ℤ L) (t : Fin R → ℤ) :
    ‖phiOf (vb b) (fun i => (t i : ℝ))‖ = eNorm (latEmb b t) := by
  rw [latEmb_apply, phiOf_norm]

/-- `ballCount` for `L` equals the coefficient-space count for the coefficient map. -/
theorem ballCount_eq_latCount (b : Module.Basis (Fin R) ℤ L) (T : ℝ) :
    ballCount L T = latCount (phiOf (vb b)) T := by
  rw [ballCount, latCount, latSet]
  refine (Set.ncard_congr (fun t _ => latEmb b t) ?_ ?_ ?_).symm
  · intro t ht
    refine ⟨(b.equivFun.symm t : L).2, ?_⟩
    have ht' : ‖phiOf (vb b) (fun i => (t i : ℝ))‖ ≤ T := ht
    rw [latEmb_norm b t] at ht'
    exact ht'
  · intro t t' _ _ h
    exact latEmb_injective b h
  · intro v hv
    obtain ⟨hvL, hvT⟩ := hv
    refine ⟨b.equivFun ⟨v, hvL⟩, ?_, latEmb_equivFun b ⟨v, hvL⟩⟩
    change ‖phiOf (vb b) (fun i => ((b.equivFun ⟨v, hvL⟩) i : ℝ))‖ ≤ T
    rw [latEmb_norm b (b.equivFun ⟨v, hvL⟩), latEmb_equivFun]
    exact hvT

/-- The successive minima of `L` are the successive minima of the coefficient lattice. -/
theorem lam_eq_latMin (b : Module.Basis (Fin R) ℤ L) (i : ℕ) :
    lam L i = latMin (phiOf (vb b)) i := by
  rw [lam, latMin]
  congr 1
  ext r
  constructor
  · rintro ⟨hr, f, hfL, hfind, hfr⟩
    set g : Fin i → (Fin R → ℤ) := fun j => b.equivFun ⟨f j, hfL j⟩ with hg
    have hcomp : (latEmb b) ∘ g = f := by
      funext j
      rw [Function.comp_apply, hg, latEmb_equivFun]
    refine ⟨hr, g, ?_, fun j => ?_⟩
    · refine LinearIndependent.of_comp (latEmb b) ?_
      rw [hcomp]; exact hfind
    · rw [latEmb_norm b (g j), hg, latEmb_equivFun]
      exact hfr j
  · rintro ⟨hr, g, hgind, hgr⟩
    refine ⟨hr, (fun j => latEmb b (g j)), fun j => (b.equivFun.symm (g j) : L).2,
      ?_, fun j => ?_⟩
    · exact LinearIndependent.map' hgind (latEmb b)
        (LinearMap.ker_eq_bot.mpr (latEmb_injective b))
    · rw [← latEmb_norm b (g j)]
      exact hgr j

end Transport

end Work.HP.Sig2Rec
