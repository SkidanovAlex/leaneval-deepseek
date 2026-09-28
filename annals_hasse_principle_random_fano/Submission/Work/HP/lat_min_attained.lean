import Mathlib
import Submission.Work.HP.GonLib

/-!
# The first successive minimum of a coefficient lattice is attained

For an injective `ℝ`-linear presentation `Φ : (Fin R → ℝ) →ₗ[ℝ] EuclideanSpace ℝ ι` of a rank-`R`
lattice (`Work.HP.LatMap`), the first successive minimum `Work.HP.latMin Φ 1` — the least norm of a
nonzero lattice vector — is attained, and it is attained by a *primitive* coefficient vector.

The lattice is discrete: the set of coefficient vectors of lattice points inside a ball is finite
(`latVec_finite`), because an injective linear map on a finite-dimensional space is anti-Lipschitz.
-/

set_option autoImplicit false

noncomputable section

open Finset

namespace Work.HP

section aux
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Finitely many integer vectors have image of norm at most `c` under an injective presentation. -/
lemma latVec_finite {R : ℕ} (Φ : LatMap (ι := ι) R) (hΦ : Function.Injective Φ) (c : ℝ) :
    {t : Fin R → ℤ | ‖Φ (fun i => (t i : ℝ))‖ ≤ c}.Finite := by
  classical
  obtain ⟨K, -, hK⟩ := Φ.exists_antilipschitzWith (LinearMap.ker_eq_bot.mpr hΦ)
  refine (Set.Finite.pi fun _ : Fin R => Set.finite_Icc (-⌈(K : ℝ) * c⌉) ⌈(K : ℝ) * c⌉).subset ?_
  intro t ht
  rw [Set.mem_pi]
  intro i _
  rw [Set.mem_Icc]
  have hb : |(t i : ℝ)| ≤ (K : ℝ) * c := by
    have h1 : ‖(t i : ℝ)‖ ≤ ‖fun j : Fin R => (t j : ℝ)‖ :=
      norm_le_pi_norm (fun j : Fin R => (t j : ℝ)) i
    have h2 : ‖fun j : Fin R => (t j : ℝ)‖ ≤ (K : ℝ) * ‖Φ (fun j : Fin R => (t j : ℝ))‖ := by
      have := hK.le_mul_dist (fun j : Fin R => (t j : ℝ)) 0
      simpa [dist_zero_right, map_zero] using this
    calc |(t i : ℝ)| = ‖(t i : ℝ)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fun j : Fin R => (t j : ℝ)‖ := h1
      _ ≤ (K : ℝ) * ‖Φ (fun j : Fin R => (t j : ℝ))‖ := h2
      _ ≤ (K : ℝ) * c := mul_le_mul_of_nonneg_left ht K.coe_nonneg
  obtain ⟨hlo, hhi⟩ := abs_le.mp hb
  constructor
  · have hcast : ((-⌈(K : ℝ) * c⌉ : ℤ) : ℝ) ≤ ((t i : ℤ) : ℝ) := by
      push_cast
      calc -(⌈(K : ℝ) * c⌉ : ℝ) ≤ -((K : ℝ) * c) := neg_le_neg (Int.le_ceil _)
        _ ≤ (t i : ℝ) := hlo
    exact Int.cast_le.mp hcast
  · have hcast : ((t i : ℤ) : ℝ) ≤ ((⌈(K : ℝ) * c⌉ : ℤ) : ℝ) :=
      hhi.trans (Int.le_ceil _)
    exact Int.cast_le.mp hcast

/-- The gcd of a finite set of integers is nonnegative. -/
private lemma int_finset_gcd_nonneg {β : Type*} (s : Finset β) (f : β → ℤ) : 0 ≤ s.gcd f := by
  have h : |s.gcd f| = s.gcd f := by rw [Int.abs_eq_normalize, Finset.normalize_gcd]
  exact h ▸ abs_nonneg _

omit [DecidableEq ι] in
/-- A nonzero lattice vector of minimal norm is primitive. -/
lemma minimal_is_prim {R : ℕ} (hR : 1 ≤ R) (Φ : LatMap (ι := ι) R) (hΦ : Function.Injective Φ)
    {u : Fin R → ℤ} (hu : u ≠ 0)
    (hmin : ∀ t : Fin R → ℤ, t ≠ 0 → ‖Φ (fun i => (u i : ℝ))‖ ≤ ‖Φ (fun i => (t i : ℝ))‖) :
    IsPrim u := by
  classical
  have huniv : (Finset.univ : Finset (Fin R)).Nonempty := ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  unfold IsPrim
  by_contra hc
  obtain ⟨v, hv, hv1⟩ := Finset.extract_gcd (s := Finset.univ) u huniv
  have hvne : v ≠ 0 := by
    intro h
    have h0 : Finset.univ.gcd v = 0 := by
      rw [h]
      exact Finset.gcd_eq_zero_iff.mpr (fun x _ => rfl)
    rw [h0] at hv1
    exact one_ne_zero hv1.symm
  have hg0 : Finset.univ.gcd u ≠ 0 := by
    intro h
    exact hu (funext fun i => (Finset.gcd_eq_zero_iff.mp h) i (Finset.mem_univ i))
  have hgpos : (0 : ℤ) ≤ Finset.univ.gcd u := int_finset_gcd_nonneg _ _
  have hg2 : (2 : ℤ) ≤ |Finset.univ.gcd u| := by
    have h1 : 1 ≤ Finset.univ.gcd u := by omega
    have h3 : 2 ≤ Finset.univ.gcd u := by omega
    rw [abs_of_nonneg hgpos]
    exact h3
  have hcast : (fun i => (u i : ℝ))
      = ((Finset.univ.gcd u : ℤ) : ℝ) • (fun i => (v i : ℝ)) := by
    funext i
    rw [Pi.smul_apply, smul_eq_mul, hv i (Finset.mem_univ i), Int.cast_mul]
  have hnorm : ‖Φ (fun i => (u i : ℝ))‖
      = ((|Finset.univ.gcd u| : ℤ) : ℝ) * ‖Φ (fun i => (v i : ℝ))‖ := by
    rw [hcast, map_smul, norm_smul, Real.norm_eq_abs, ← Int.cast_abs]
  have hvpos : 0 < ‖Φ (fun i => (v i : ℝ))‖ := by
    rw [norm_pos_iff]
    intro hcon
    exact hvne (funext fun i => by
      have h1 : (fun j : Fin R => (v j : ℝ)) = 0 := by
        apply hΦ
        simpa using hcon
      have h2 : (v i : ℝ) = 0 := congrFun h1 i
      exact_mod_cast h2)
  have hbig : ‖Φ (fun i => (v i : ℝ))‖ < ‖Φ (fun i => (u i : ℝ))‖ := by
    rw [hnorm]
    have h2 : (2 : ℝ) ≤ ((|Finset.univ.gcd u| : ℤ) : ℝ) := by exact_mod_cast hg2
    calc ‖Φ (fun i => (v i : ℝ))‖ < 2 * ‖Φ (fun i => (v i : ℝ))‖ := by linarith
      _ ≤ ((|Finset.univ.gcd u| : ℤ) : ℝ) * ‖Φ (fun i => (v i : ℝ))‖ :=
          mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
  exact absurd (hmin v hvne) (not_le.mpr hbig)

end aux

theorem lat_min_attained {ι : Type*} [Fintype ι] [DecidableEq ι] {R : ℕ} (hR : 1 ≤ R)
    (Φ : LatMap (ι := ι) R) (hΦ : Function.Injective Φ) :
    ∃ u : Fin R → ℤ, u ≠ 0 ∧ IsPrim u ∧ ‖Φ (fun i => (u i : ℝ))‖ = latMin Φ 1 := by
  classical
  let i₀ : Fin R := ⟨0, by omega⟩
  let t₀ : Fin R → ℤ := Pi.single i₀ 1
  have ht₀ne : t₀ ≠ 0 := by
    intro h
    have h1 : t₀ i₀ = 1 := Pi.single_eq_same i₀ 1
    rw [h] at h1
    exact one_ne_zero (show (1 : ℤ) = 0 from by simpa using h1.symm)
  let c₀ : ℝ := ‖Φ (fun i => (t₀ i : ℝ))‖
  have hFfin : {t : Fin R → ℤ | t ≠ 0 ∧ ‖Φ (fun i => (t i : ℝ))‖ ≤ c₀}.Finite :=
    (latVec_finite Φ hΦ c₀).subset (fun t ht => ht.2)
  have hFne : ({t : Fin R → ℤ | t ≠ 0 ∧ ‖Φ (fun i => (t i : ℝ))‖ ≤ c₀} : Set (Fin R → ℤ)).Nonempty :=
    ⟨t₀, ht₀ne, le_refl _⟩
  obtain ⟨u, huF, hminF⟩ :=
    Set.exists_min_image {t : Fin R → ℤ | t ≠ 0 ∧ ‖Φ (fun i => (t i : ℝ))‖ ≤ c₀}
      (fun t => ‖Φ (fun i => (t i : ℝ))‖) hFfin hFne
  have hune : u ≠ 0 := huF.1
  have hmin : ∀ t : Fin R → ℤ, t ≠ 0 → ‖Φ (fun i => (u i : ℝ))‖ ≤ ‖Φ (fun i => (t i : ℝ))‖ := by
    intro t ht
    by_cases htc : ‖Φ (fun i => (t i : ℝ))‖ ≤ c₀
    · exact hminF t ⟨ht, htc⟩
    · push Not at htc
      exact huF.2.trans htc.le
  refine ⟨u, hune, minimal_is_prim hR Φ hΦ hune hmin, ?_⟩
  have hmemS : ‖Φ (fun i => (u i : ℝ))‖
      ∈ {r : ℝ | 0 ≤ r ∧ ∃ t : Fin R → ℤ, t ≠ 0 ∧ ‖Φ (fun i => (t i : ℝ))‖ ≤ r} :=
    ⟨norm_nonneg _, u, hune, le_refl _⟩
  have hbdd : BddBelow {r : ℝ | 0 ≤ r ∧ ∃ t : Fin R → ℤ, t ≠ 0 ∧ ‖Φ (fun i => (t i : ℝ))‖ ≤ r} :=
    ⟨0, fun r hr => hr.1⟩
  have hneS : ({r : ℝ | 0 ≤ r ∧ ∃ t : Fin R → ℤ, t ≠ 0 ∧
      ‖Φ (fun i => (t i : ℝ))‖ ≤ r} : Set ℝ).Nonempty := ⟨_, hmemS⟩
  have hlat : latMin Φ 1 = sInf {r : ℝ | 0 ≤ r ∧ ∃ t : Fin R → ℤ, t ≠ 0 ∧
      ‖Φ (fun i => (t i : ℝ))‖ ≤ r} := by
    unfold latMin
    congr 1
    ext r
    constructor
    · rintro ⟨hr0, f, hf, hfr⟩
      exact ⟨hr0, f 0, hf.ne_zero 0, hfr 0⟩
    · rintro ⟨hr0, t, ht, htr⟩
      exact ⟨hr0, fun _ => t, by
        rw [Fintype.linearIndependent_iff]
        intro g hg i
        have hg0 : g 0 = 0 := by
          have hsum : g 0 • t = 0 := by simpa [Fin.sum_univ_one] using hg
          rcases smul_eq_zero.mp hsum with h | h
          · exact h
          · exact absurd h ht
        rw [Fin.eq_zero i]
        exact hg0, fun _ => htr⟩
  rw [hlat]
  exact le_antisymm
    (le_csInf hneS (fun b hb => by
      obtain ⟨t, ht, htb⟩ := hb.2
      exact (hmin t ht).trans htb))
    (csInf_le hbdd hmemS)

end Work.HP
