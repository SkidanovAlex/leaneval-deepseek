import Mathlib
import Submission.Work.BrauerSuzuki.Q8.Ctx
import Submission.Work.BrauerSuzuki.Q8.Eta
import Submission.Work.BrauerSuzuki.Q8.Eta2
import Submission.Work.CharCore.Basic
import Submission.Work.CharCore.irr_orthonormal
import Submission.Work.CharCore.star_Irr
import Submission.Work.Clifford.galoisChar_mem_Irr
import Submission.Work.Clifford.galois_char_apply
import Submission.Work.Clifford.card_Irr_eq_card_conjClasses
import Submission.Work.Tame.ft10_4
import Submission.Work.NormalComplement.rat_eq_int_of_isIntegral
import Submission.Work.BrauerSuzuki.Q8.step7a_galois_fixed_rat
import Submission.Work.BrauerSuzuki.Q8.step7a_rat_involution
import Submission.Work.BrauerSuzuki.Q8.step7a_numeric

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Glauberman (1974), step (7)(a): the values of the `χᵢ` are rational integers

With `η = 1_G + ∑ εᵢ χᵢ` (`Q8/Eta2`), `η` takes the values `4` on `B` and `0` off `B`, so `η`
is rational-valued; hence every ring automorphism of `ℂ` permutes the irreducible characters
`χ₁, χ₂, χ₃` (the constituents of `η - 1_G`), preserving the signs `εᵢ`.  If `σ` moved `χᵢ` to
`χⱼ`, `i ≠ j`, then `χⱼ(1) = χᵢ(1)` (the degree is an integer) and `χⱼ(x²) = χᵢ(x²)` (`x²` is an
involution, so `χ(x²) ∈ ℚ`), so `xⱼ = xᵢ` and `zⱼ = zᵢ`, `εⱼ = εᵢ`; the three numerical
relations of step (5) then give `1 = 0` (the numerical contradiction
`Work.BrauerSuzuki.Q8.step7a_numeric`, following Glauberman's step (7)(a)).  Hence every `χᵢ` is
fixed by every automorphism of `ℂ`; as its values lie in `ℚ(ζ_|G|)`, they are rational
(`Work.BrauerSuzuki.Q8.step7a_galois_fixed_rat`).  Being also algebraic integers they are
integers.
-/

set_option autoImplicit false

namespace Work.BrauerSuzuki.Q8

open Classical

/-- `cfInner` is equivariant for a ring automorphism `σ` of `ℂ` applied to the *first*
argument, provided the second argument is fixed by `σ` and is real. -/
theorem cfInner_map_ringEquiv {G : Type*} [Group G] [Fintype G] (σ : ℂ ≃+* ℂ) (f η : G → ℂ)
    (hη : ∀ g, σ (η g) = η g) (hηs : ∀ g, starRingEnd ℂ (η g) = η g) :
    Work.CharCore.cfInner (fun g => σ (f g)) η = σ (Work.CharCore.cfInner f η) := by
  rw [Work.CharCore.cfInner_apply, Work.CharCore.cfInner_apply, map_mul, map_inv₀, map_natCast,
    map_sum]
  congr 1
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [map_mul]
  rw [hηs g, hη g]

/-- The bridge between the `Finset`-based `Work.CharCore.Irr` and the set-based
`Work.Clifford.Irr`. -/
theorem mem_Irr_clifford_iff {G : Type*} [Group G] [Fintype G] {χ : G → ℂ} :
    χ ∈ Work.CharCore.Irr G ↔ χ ∈ Work.Clifford.Irr G :=
  Work.Clifford.mem_Irr_iff_fdrep_aux χ

/-- The Galois twist `g ↦ σ (χ g)` of an irreducible character is irreducible
(`Work.CharCore` form). -/
theorem galoisTwist_mem_Irr_charCore {G : Type*} [Group G] [Fintype G] (σ : ℂ ≃+* ℂ)
    {χ : G → ℂ} (hχ : χ ∈ Work.CharCore.Irr G) :
    (fun g => σ (χ g)) ∈ Work.CharCore.Irr G :=
  (mem_Irr_clifford_iff).mpr
    (Work.Clifford.galoisChar_mem_Irr σ ((mem_Irr_clifford_iff).mp hχ))

open Classical in
theorem step7a_values_int {G : Type*} [Group G] [Fintype G] {x : G} {S : Sylow 2 G}
    (h : Work.BrauerSuzuki.Q8.Ctx G x S) (χ : Fin 3 → G → ℂ) (ε : Fin 3 → ℂ)
    (hIrr : ∀ i, χ i ∈ Work.CharCore.Irr G) (hne : ∀ i, χ i ≠ (fun _ => (1 : ℂ)))
    (hdist : ∀ i j, i ≠ j → χ i ≠ χ j)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hη : h.eta = (fun _ => (1 : ℂ)) + ∑ i, ε i • χ i)
    (hx1 : (1 : ℂ) + ∑ i, ε i * χ i 1 = 0)
    (hx2 : ∑ i, ε i * (χ i 1 - χ i (x ^ 2)) = 0)
    (hx3 : ∑ i, ε i * (χ i 1 - χ i (x ^ 2)) ^ 2 / (χ i 1) = 0)
    (hzpos : ∀ i, 0 < ((χ i 1 - χ i (x ^ 2)) : ℂ).re) :
    ∀ i : Fin 3, ∀ g : G, ∃ n : ℤ, χ i g = (n : ℂ) := by
  classical
  -- ### Elementary facts about the degrees `x_i = χᵢ(1)`
  have hdeg : ∀ i : Fin 3, ∃ d : ℕ, χ i 1 = (d : ℂ) :=
    fun i => Work.CharCore.exists_natCast_apply_one (hIrr i)
  have hxne : ∀ i : Fin 3, χ i 1 ≠ 0 := by
    intro i
    rw [Work.CharCore.irrDeg_spec (hIrr i)]
    exact Work.CharCore.irrDeg_ne_zero (hIrr i)
  have hσ1 : ∀ (σ : ℂ ≃+* ℂ) (i : Fin 3), σ (χ i 1) = χ i 1 := by
    intro σ i
    obtain ⟨d, hd⟩ := hdeg i
    rw [hd, map_natCast]
  -- `x²` is an involution, so `χᵢ(x²)` is rational and hence fixed by every `σ`.
  have hx2sq : (x ^ 2) ^ 2 = 1 := by
    rw [← pow_mul, show 2 * 2 = 4 from rfl, ← h.hx4]
    exact pow_orderOf_eq_one x
  have hσ2 : ∀ (σ : ℂ ≃+* ℂ) (i : Fin 3), σ (χ i (x ^ 2)) = χ i (x ^ 2) := by
    intro σ i
    obtain ⟨q, hq⟩ := step7a_rat_involution (hIrr i) hx2sq
    rw [hq, map_ratCast]
  -- ### `η` is `{0,4}`-valued, hence real and rational
  have heta_val : ∀ g : G, h.eta g = 0 ∨ h.eta g = 4 := by
    intro g
    by_cases hg : g ∈ Bset x
    · exact Or.inr (h.eta_apply_Bset hg)
    · exact Or.inl (h.eta_apply_notMem_Bset hg)
  have heta_star : ∀ g : G, starRingEnd ℂ (h.eta g) = h.eta g := by
    intro g
    rcases heta_val g with h0 | h4
    · rw [h0, map_zero]
    · rw [h4]
      exact Complex.conj_ofNat 4
  have heta_sigma : ∀ (σ : ℂ ≃+* ℂ) (g : G), σ (h.eta g) = h.eta g := by
    intro σ g
    rcases heta_val g with h0 | h4
    · rw [h0, map_zero]
    · rw [h4]
      exact map_ofNat σ 4
  -- ### Step 1: `(χᵢ, η) = εᵢ`
  have hinner : ∀ i : Fin 3, Work.CharCore.cfInner (χ i) h.eta = ε i := by
    intro i
    have hprin : Work.CharCore.cfInner (χ i) (fun _ : G => (1 : ℂ)) = 0 := by
      rw [Work.CharCore.irr_orthonormal (χ i) (fun _ : G => (1 : ℂ)) (hIrr i)
        Work.CharCore.principalChar_mem_Irr]
      simp [hne i]
    rw [hη, Work.CharCore.cfInner_add_right, Work.CharCore.cfInner_sum_smul_right, hprin,
      zero_add]
    have hstep : ∀ j : Fin 3, starRingEnd ℂ (ε j) * Work.CharCore.cfInner (χ i) (χ j)
        = starRingEnd ℂ (ε j) * (if χ i = χ j then 1 else 0) := by
      intro j
      rw [Work.CharCore.irr_orthonormal (χ i) (χ j) (hIrr i) (hIrr j)]
    rw [Finset.sum_congr rfl (fun j _ => hstep j)]
    rw [Finset.sum_eq_single i]
    · rcases hε i with h1 | h1 <;> simp [h1]
    · intro j _ hj
      rw [if_neg (hdist i j (Ne.symm hj)), mul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  -- ### Step 2: Galois equivariance, `(σ ∘ χᵢ, η) = εᵢ`
  have hinnerσ : ∀ (σ : ℂ ≃+* ℂ) (i : Fin 3),
      Work.CharCore.cfInner (fun g => σ (χ i g)) h.eta = ε i := by
    intro σ i
    rw [cfInner_map_ringEquiv σ (χ i) h.eta (heta_sigma σ) heta_star, hinner i]
    rcases hε i with h1 | h1 <;> simp [h1]
  -- ### Step 3: `σ ∘ χᵢ` is one of the `χⱼ`, with matching sign
  have hext : ∀ (σ : ℂ ≃+* ℂ) (i : Fin 3), ∃ j : Fin 3,
      (fun g => σ (χ i g)) = χ j ∧ ε j = ε i := by
    intro σ i
    have hψne : (fun g => σ (χ i g)) ≠ (fun _ : G => (1 : ℂ)) := by
      intro hc
      apply hne i
      funext g
      have h1 : σ (χ i g) = σ (1 : ℂ) := by
        have h2 := congrFun hc g
        simpa using h2
      exact σ.injective h1
    have hexp : Work.CharCore.cfInner (fun g => σ (χ i g)) h.eta
        = (if (fun g => σ (χ i g)) = (fun _ : G => (1 : ℂ)) then 1 else 0)
          + ∑ j : Fin 3,
              starRingEnd ℂ (ε j) * (if (fun g => σ (χ i g)) = χ j then 1 else 0) := by
      rw [hη, Work.CharCore.cfInner_add_right, Work.CharCore.cfInner_sum_smul_right]
      congr 1
      · rw [Work.CharCore.irr_orthonormal _ _ (galoisTwist_mem_Irr_charCore σ (hIrr i))
          Work.CharCore.principalChar_mem_Irr]
      · refine Finset.sum_congr rfl fun j _ => ?_
        rw [Work.CharCore.irr_orthonormal _ _ (galoisTwist_mem_Irr_charCore σ (hIrr i))
          (hIrr j)]
    rw [hinnerσ σ i, if_neg hψne, zero_add] at hexp
    have hex : ∃ j : Fin 3, (fun g => σ (χ i g)) = χ j := by
      by_contra hcon
      push_neg at hcon
      have hzero : (∑ j : Fin 3,
          starRingEnd ℂ (ε j) * (if (fun g => σ (χ i g)) = χ j then 1 else 0)) = 0 := by
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [if_neg (hcon j), mul_zero]
      rw [hzero] at hexp
      have hne0 : ε i ≠ 0 := by rcases hε i with h1 | h1 <;> simp [h1]
      exact hne0 hexp
    obtain ⟨j, hψj⟩ := hex
    have hsumj : (∑ j' : Fin 3,
        starRingEnd ℂ (ε j') * (if (fun g => σ (χ i g)) = χ j' then 1 else 0)) = ε j := by
      rw [Finset.sum_eq_single j]
      · rw [if_pos hψj, mul_one]
        rcases hε j with h1 | h1 <;> simp [h1]
      · intro j' _ hj'
        rw [if_neg (fun hcontra => hdist j j' (Ne.symm hj') (hψj.symm.trans hcontra)),
          mul_zero]
      · intro hj
        exact absurd (Finset.mem_univ j) hj
    rw [hsumj] at hexp
    exact ⟨j, hψj, hexp.symm⟩
  -- ### Step 4: the twist is trivial
  have hfixσ : ∀ (σ : ℂ ≃+* ℂ) (i : Fin 3), (fun g => σ (χ i g)) = χ i := by
    intro σ i
    obtain ⟨j, hψj, hεji⟩ := hext σ i
    by_cases hji : j = i
    · rwa [hji] at hψj
    · exfalso
      have hji' : i ≠ j := fun hh => hji hh.symm
      have hxij : χ i 1 = χ j 1 := by rw [← congrFun hψj 1, hσ1 σ i]
      have hyij : χ i (x ^ 2) = χ j (x ^ 2) := by rw [← congrFun hψj (x ^ 2), hσ2 σ i]
      exact step7a_numeric (p := i) (q := j) (e := ε) (x := fun i => χ i 1)
        (z := fun i => χ i 1 - χ i (x ^ 2)) hε hxne (fun i => hzpos i) hx1 hx2 hx3 hji'
        hεji.symm hxij (by simp only [hxij, hyij])
  -- ### Step 5: rationality of the values
  have hrat : ∀ (i : Fin 3) (g : G), ∃ q : ℚ, χ i g = (q : ℂ) := by
    intro i g
    have hfix : ∀ σ : ℂ ≃+* ℂ, σ (χ i g) = χ i g :=
      fun σ => congrFun (hfixσ σ i) g
    have hc : χ i g ∈ Algebra.adjoin ℚ ({z : ℂ | z ^ (Nat.card G) = 1} : Set ℂ) :=
      Work.Tame.irr_apply_mem_adjoin (hIrr i) (Nat.card_pos (α := G)) (orderOf_dvd_natCard g)
    exact step7a_galois_fixed_rat (Nat.card_pos (α := G)) hc hfix
  -- ### Step 6: rationality + integrality ⟹ integrality
  intro i g
  obtain ⟨q, hq⟩ := hrat i g
  have hint : IsIntegral ℤ (χ i g) := by
    obtain ⟨N, _, hNχ⟩ := Work.CharCore.exists_mem_irrSubmodules_of_mem_Irr (hIrr i)
    have h1 := Representation.isIntegral_character (Work.CharCore.submoduleRep N) g
    rwa [hNχ] at h1
  obtain ⟨m, hm⟩ := Work.NormalComplement.rat_eq_int_of_isIntegral (q := q) (by rw [← hq]; exact hint)
  exact ⟨m, by rw [hq, hm]; norm_num⟩

end Work.BrauerSuzuki.Q8
