import Mathlib
import Submission.Work.BrauerSuzuki.Defs
import Submission.Work.BrauerSuzuki.Q8.Ctx
import Submission.Work.BrauerSuzuki.Q8.Card
import Submission.Work.BrauerSuzuki.Q8.LamEta
import Submission.Work.BrauerSuzuki.Q8.Zeta
import Submission.Work.BrauerSuzuki.Q8.Eta
import Submission.Work.BrauerSuzuki.Q8.Eta2
import Submission.Work.BrauerSuzuki.Q8.IndTwo
import Submission.Work.BrauerSuzuki.Q8.GroupSetup
import Submission.Work.BrauerSuzuki.Q8.Cstar_Nstar_Astar
import Submission.Work.BrauerSuzuki.Q8.sylow_two_structure_and_centralizer
import Submission.Work.BrauerSuzuki.Q8.strongProved
import Submission.Work.BrauerSuzuki.Q8.Bset_facts
import Submission.Work.BrauerSuzuki.Q8.step3d_counting
import Submission.Work.BrauerSuzuki.Q8.step4a_ker_center
import Submission.Work.BrauerSuzuki.Q8.step4b_frobenius
import Submission.Work.BrauerSuzuki.Q8.step4b_center
import Submission.Work.BrauerSuzuki.Q8.step6_inner_eta
import Submission.Work.BrauerSuzuki.Q8.step6_inner_eta_classfun
import Submission.Work.BrauerSuzuki.Q8.step7a_values_int
import Submission.Work.BrauerSuzuki.Q8.step7b_values_conj
import Submission.Work.BrauerSuzuki.Q8.step8_odd
import Submission.Work.BrauerSuzuki.Q8.step9_chi_x
import Submission.Work.BrauerSuzuki.Q8.step9_deg_two
import Submission.Work.BrauerSuzuki.Q8.step10_character_congruences
import Submission.Work.BrauerSuzuki.Characters.vchar_of_norm_four
import Submission.Work.BrauerSuzuki.Arith.glauberman_step11
import Submission.Work.BrauerSuzuki.Sylow.genQuaternionData_quotient_oddCore
import Submission.Work.ThreePoints.oddCore_quotient_oddCore
import Submission.Work.CharCore.norm_char_le
import Submission.Work.NPC.All

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Assembly of Glauberman's `Q₈` case of Brauer–Suzuki

This file assembles the steps (1)–(11) of Glauberman, *On groups with a quaternion Sylow
2-subgroup*, Illinois J. Math. **18** (1974) 60–65 (see `REFS/brauer_suzuki.md` §3) into the
proof of `BrauerSuzukiQ8Strong`:

* `character_contradiction` is the heart of the argument: for a minimal counterexample with
  `O(G) = ⊥`, `|Z(G)| ≠ 2` and all elements of order `4` conjugate, the generalized character
  `η = Ind_{N*}^G ζ` (steps (2), (3)) yields irreducible characters `χᵢ` with
  `η = 1 + Σ εᵢ χᵢ`; steps (3)(d), (5)–(11) then produce the contradiction.
* `no_counterexample` is the minimal-counterexample argument for `O(G) = ⊥`:
  `|Z(G)| ≠ 2` (else `G` has a unique involution), all elements of order `4` are conjugate
  (else Frobenius' normal `2`-complement theorem makes `|Z(G)| = 2`), and then
  `character_contradiction` applies.
* `main_aux` is the strong induction on `|G|`: if `O(G) ≠ 1`, pass to `G ⧸ O(G)` (where
  `O(G ⧸ O(G)) = 1` and the Sylow `2`-subgroups are again `Q₈`), otherwise use
  `no_counterexample`.
-/

set_option autoImplicit false

open Classical
open scoped Pointwise

namespace Work.BrauerSuzuki.Q8

variable {G : Type*} [Group G]

/-- `x ^ 2` is an involution for `x` of order `4`. -/
theorem sq_orderOf_two {x : G} (hx4 : orderOf x = 4) : orderOf (x ^ 2) = 2 := by
  have h1 : (x ^ 2) ^ 2 = 1 := by
    rw [← pow_mul, show 2 * 2 = 4 by norm_num, ← hx4]
    exact pow_orderOf_eq_one x
  refine orderOf_eq_prime h1 ?_
  intro hc
  have hdvd : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hc
  rw [hx4] at hdvd
  omega

/-- A character of degree `1` whose value at an involution differs from its degree would give
`x² ∉ ker χ`; but a linear character kills the derived subgroup of a quaternion Sylow
`2`-subgroup, which is exactly `⟨x²⟩`.  Hence `2 ≤ irrDeg χ` (Glauberman (1974), step (9)). -/
theorem re_pos_sub_of_ne {G : Type*} [Group G] [Fintype G] {χ : G → ℂ}
    (hχ : χ ∈ Work.CharCore.Irr G) {t : G} (ht : t ^ 2 = 1) (h : χ t ≠ χ 1) :
    0 < (χ 1 - χ t).re := by
  obtain ⟨q, hq⟩ := step7a_rat_involution hχ ht
  have hnorm := Work.CharCore.norm_char_le hχ t
  have h1 : χ 1 = (Work.CharCore.irrDeg χ : ℂ) := Work.CharCore.irrDeg_spec hχ
  rw [hq] at hnorm
  have hnorm2 : |(q : ℝ)| ≤ (Work.CharCore.irrDeg χ : ℝ) := by
    rwa [Complex.norm_ratCast] at hnorm
  have hne : (q : ℝ) ≠ (Work.CharCore.irrDeg χ : ℝ) := by
    intro hc
    apply h
    have hcq : (q : ℂ) = ((Work.CharCore.irrDeg χ : ℕ) : ℂ) := by
      rw [← Complex.ofReal_ratCast, ← Complex.ofReal_natCast, hc]
    rw [hq, h1]
    exact hcq
  have hlt : (q : ℝ) < (Work.CharCore.irrDeg χ : ℝ) :=
    lt_of_le_of_ne (le_trans (le_abs_self (q : ℝ)) hnorm2) hne
  have hsub : χ 1 - χ t = (((Work.CharCore.irrDeg χ : ℝ) - (q : ℝ) : ℝ) : ℂ) := by
    rw [h1, hq]
    push_cast
    ring
  rw [hsub, Complex.ofReal_re]
  linarith

/-- **Glauberman (1974), step (5)(b).**  With `xᵢ = χᵢ(1)`, `yᵢ = χᵢ(x²)` and `zᵢ = xᵢ - yᵢ`,
`1 + Σ εᵢxᵢ = Σ εᵢzᵢ = Σ εᵢ(zᵢ²/xᵢ) = 0`.  The first two come from `η(1) = η(x²) = 0`, the
third from the counting identity (3)(d) at `u = x²` together with the expansion
`yᵢ²/xᵢ = zᵢ²/xᵢ - 2zᵢ + xᵢ`. -/
theorem step5_identities {G : Type*} [Group G] [Fintype G] {x : G} {S : Sylow 2 G}
    (h : Ctx G x S) (χ : Fin 3 → G → ℂ) (ε : Fin 3 → ℂ)
    (hIrr : ∀ i, χ i ∈ Work.CharCore.Irr G)
    (hη : h.eta = (fun _ => (1 : ℂ)) + ∑ i, ε i • χ i)
    (hB : ∀ y : G, y ∈ Bset x → ¬ Odd (orderOf y))
    (hmul : ∀ a b : G, orderOf a = 2 → orderOf b = 2 → Odd (orderOf (a * b)))
    (hx2 : orderOf (x ^ 2) = 2)
    (h1B : (1 : G) ∉ Bset x) (hx2B : x ^ 2 ∉ Bset x)
    (hdegne : ∀ i, χ i 1 ≠ 0) :
    ((1 : ℂ) + ∑ i, ε i * χ i 1 = 0) ∧
      (∑ i, ε i * (χ i 1 - χ i (x ^ 2)) = 0) ∧
      (∑ i, ε i * (χ i 1 - χ i (x ^ 2)) ^ 2 / (χ i 1) = 0) := by
  have hpt : ∀ z : G, h.eta z = 1 + ∑ i, ε i * χ i z := by
    intro z
    have h1 := congrFun hη z
    simpa only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply] using h1
  have hE1 : (1 : ℂ) + ∑ i, ε i * χ i 1 = 0 := by
    have h1 := h.eta_apply_notMem_Bset (g := (1 : G)) h1B
    rw [hpt 1] at h1
    exact h1
  have hE2 : (1 : ℂ) + ∑ i, ε i * χ i (x ^ 2) = 0 := by
    have h1 := h.eta_apply_notMem_Bset (g := x ^ 2) hx2B
    rw [hpt (x ^ 2)] at h1
    exact h1
  have hA : ∑ i, ε i * χ i 1 = -1 := by
    have h := hE1
    rw [add_comm] at h
    exact eq_neg_of_add_eq_zero_left h
  have hA2 : ∑ i, ε i * χ i (x ^ 2) = -1 := by
    have h := hE2
    rw [add_comm] at h
    exact eq_neg_of_add_eq_zero_left h
  have hzsum : ∑ i, ε i * (χ i 1 - χ i (x ^ 2)) = 0 := by
    have hsplit : ∑ i, ε i * (χ i 1 - χ i (x ^ 2))
        = (∑ i, ε i * χ i 1) - ∑ i, ε i * χ i (x ^ 2) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [hsplit, hA, hA2]
    ring
  refine ⟨hE1, hzsum, ?_⟩
  have h3d := step3d_counting h χ ε hIrr hη hB hmul hx2
  have h3dz : ∑ i, ε i * (χ i (x ^ 2)) ^ 2 / (χ i 1) = -1 := by
    have h := h3d
    rw [add_comm] at h
    exact eq_neg_of_add_eq_zero_left h
  have hkey : ∀ i : Fin 3, ε i * (χ i 1 - χ i (x ^ 2)) ^ 2 / (χ i 1)
      = (ε i * χ i 1 - 2 * (ε i * χ i (x ^ 2)) + ε i * (χ i (x ^ 2)) ^ 2 / (χ i 1)) := by
    intro i
    field_simp [hdegne i]
    ring
  have hsplit2 : ∑ i, ε i * (χ i 1 - χ i (x ^ 2)) ^ 2 / (χ i 1)
      = (∑ i, ε i * χ i 1) - 2 * (∑ i, ε i * χ i (x ^ 2))
          + ∑ i, ε i * (χ i (x ^ 2)) ^ 2 / (χ i 1) := by
    rw [Finset.sum_congr rfl (fun i _ => hkey i), Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum]
  rw [hsplit2, hA, hA2, h3dz]
  ring

/-- The structural hypotheses of Glauberman's step (1), assembled from
`Cstar_Nstar_Astar` and `sylow_two_structure_and_centralizer`. -/
theorem ctx_of {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (d : Work.BrauerSuzuki.GenQuaternionData ↥S) (h2 : d.n = 2) {x : G}
    (hxS : x ∈ (S : Subgroup G)) (hx4 : orderOf x = 4) : Ctx G x S := by
  obtain ⟨hsup, hinf, hcomm, hodd, hleN, hsupN, hTI⟩ := Cstar_Nstar_Astar S d h2 hxS hx4
  refine ⟨hx4, hxS, ?_, hsup, hinf, hcomm, hodd, hleN, hsupN, ?_, hTI⟩
  · have h := (Work.BrauerSuzuki.Quaternion.genQuaternionData_basic d).1
    rw [h2] at h
    norm_num at h
    exact h
  · have hstruct := sylow_two_structure_and_centralizer S d h2
    refine le_antisymm ?_ ?_
    · rintro y ⟨hyS, hyC⟩
      have hcommxy : y * x = x * y :=
        (Subgroup.mem_centralizer_iff.mp hyC x (Subgroup.mem_zpowers x)).symm
      have h2pow : ∃ k : ℕ, orderOf y = 2 ^ k := by
        obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp S.isPGroup') (⟨y, hyS⟩ : ↥(S : Subgroup G))
        exact ⟨k, by
          have hcoe : orderOf y = orderOf (⟨y, hyS⟩ : ↥(S : Subgroup G)) :=
            Subgroup.orderOf_coe ⟨y, hyS⟩
          rw [hcoe]
          exact hk⟩
      exact hstruct.2.2 x hxS hx4 y hcommxy h2pow
    · refine le_inf (Subgroup.zpowers_le.mpr hxS) (Subgroup.zpowers_le.mpr ?_)
      show x ∈ Subgroup.centralizer (X x : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      rw [← zpow_add_one, ← zpow_one_add, add_comm]

/-- The projections of `η = 1 + Σ εᵢχᵢ` (Glauberman (1974), step (2)(c)) onto its
irreducible constituents. -/
theorem cfInner_eta_eq_eps {G : Type*} [Group G] [Fintype G] {x : G} {S : Sylow 2 G}
    (h : Ctx G x S) (χ : Fin 3 → G → ℂ) (ε : Fin 3 → ℂ)
    (hIrr : ∀ i, χ i ∈ Work.CharCore.Irr G)
    (hne : ∀ i, χ i ≠ (fun _ => (1 : ℂ)))
    (hdist : ∀ i j, i ≠ j → χ i ≠ χ j)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hη : h.eta = (fun _ => (1 : ℂ)) + ∑ i, ε i • χ i) (i : Fin 3) :
    Work.CharCore.cfInner (χ i) h.eta = ε i := by
  rw [hη, Work.CharCore.cfInner_add_right, Work.CharCore.cfInner_sum_smul_right]
  have hone : Work.CharCore.cfInner (χ i) (fun _ => (1 : ℂ)) = 0 := by
    rw [Work.CharCore.irr_orthonormal (χ i) (fun _ => (1 : ℂ)) (hIrr i)
      Work.CharCore.principalChar_mem_Irr, if_neg (hne i)]
  rw [hone, zero_add]
  have hsum : (∑ j : Fin 3, starRingEnd ℂ (ε j) * Work.CharCore.cfInner (χ i) (χ j))
      = starRingEnd ℂ (ε i) * Work.CharCore.cfInner (χ i) (χ i) := by
    refine Finset.sum_eq_single i ?_ ?_
    · intro j _ hj
      rw [Work.CharCore.irr_orthonormal (χ i) (χ j) (hIrr i) (hIrr j),
        if_neg (fun heq => hdist j i hj heq.symm), mul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  rw [hsum, Work.CharCore.irr_orthonormal (χ i) (χ i) (hIrr i) (hIrr i), if_pos rfl, mul_one]
  rcases hε i with h1 | h1 <;> rw [h1] <;> simp

/-- **Steps (2)–(11) of Glauberman (1974).**  A minimal counterexample with trivial odd core
cannot have `|Z(G)| ≠ 2` and all elements of order `4` conjugate: the generalized character
`η = Ind_{N*}^G ζ` decomposes as `1 + Σ εᵢχᵢ`, and the arithmetic steps (5)–(11) contradict the
character congruences of step (10). -/
theorem character_contradiction {G : Type*} [Group G] [Fintype G]
    (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S) (h2 : d.n = 2)
    {x : G} (h : Ctx G x S)
    (hO : Submission.Blueprint.oddCore G = ⊥)
    (hZ : Nat.card ↥(Subgroup.center G) ≠ 2)
    (hconj : ∀ y z : G, orderOf y = 4 → orderOf z = 4 → IsConj y z)
    (hIH : ∀ (H : Type) [Group H] [Finite H], Nat.card H < Nat.card G →
      ∀ (T : Sylow 2 H) (e : Work.BrauerSuzuki.GenQuaternionData ↥T), e.n = 2 →
      ∀ y : H, y ∈ (T : Subgroup H) → orderOf y = 4 →
      ∀ k : H, y ^ 2 * k * (y ^ 2)⁻¹ * k⁻¹ ∈ Submission.Blueprint.oddCore H) :
    False := by
  classical
  obtain ⟨χ, ε, hIrr, hne, hdist, hε, hη⟩ :=
    Work.BrauerSuzuki.Characters.vchar_of_norm_four h.isVChar_eta h.cfInner_eta_self
      h.cfInner_eta_one
  obtain ⟨h1B, hx2B, hBord, _hAord⟩ := Bset_facts h
  have hB : ∀ y : G, y ∈ Bset x → ¬ Odd (orderOf y) := by
    intro y hy hodd
    exact (Nat.not_even_iff_odd.mpr hodd)
      (even_iff_two_dvd.mpr (dvd_trans (by norm_num) (hBord y hy)))
  have hmul : ∀ a b : G, orderOf a = 2 → orderOf b = 2 → Odd (orderOf (a * b)) :=
    fun a b ha hb => odd_orderOf_mul_of_genQuaternionData S d ha hb
  have hx2 : orderOf (x ^ 2) = 2 := sq_orderOf_two h.hx4
  have hx2sq : (x ^ 2) ^ 2 = 1 := by
    rw [← pow_mul, show 2 * 2 = 4 by norm_num, ← h.hx4]
    exact pow_orderOf_eq_one x
  have hdegne : ∀ i : Fin 3, χ i 1 ≠ 0 := fun i => by
    rw [Work.CharCore.irrDeg_spec (hIrr i)]
    exact Work.CharCore.irrDeg_ne_zero (hIrr i)
  obtain ⟨hx1, hx2z, hx3z⟩ := step5_identities h χ ε hIrr hη hB hmul hx2 h1B hx2B hdegne
  -- step (4)(a): `x ^ 2 ∉ ker χᵢ`
  have hker_ne : ∀ i : Fin 3, χ i (x ^ 2) ≠ χ i 1 := by
    intro i heq
    exact hZ (step4a_ker_center S d h2 x h.hxS h.hx4 hO hconj hIH (hIrr i) (hne i) heq)
  have hzpos : ∀ i : Fin 3, 0 < ((χ i 1 - χ i (x ^ 2) : ℂ)).re := fun i =>
    re_pos_sub_of_ne (hIrr i) hx2sq (hker_ne i)
  have hdeg : ∀ i : Fin 3, 2 ≤ Work.CharCore.irrDeg (χ i) := fun i =>
    step9_deg_two S d h2 h.hxS h.hx4 (hIrr i) (hker_ne i)
  have hint : ∀ i : Fin 3, ∀ g : G, ∃ n : ℤ, χ i g = (n : ℂ) :=
    step7a_values_int h χ ε hIrr hne hdist hε hη hx1 hx2z hx3z hzpos
  -- the signs `εᵢ` as integers
  let εZ : Fin 3 → ℤ := fun i => if ε i = 1 then 1 else -1
  have hεZval : ∀ i : Fin 3, (εZ i : ℂ) = ε i := by
    intro i
    rcases hε i with h1 | h1
    · have hεZi : εZ i = 1 := by
        show (if ε i = 1 then (1 : ℤ) else -1) = 1
        rw [if_pos h1]
      rw [hεZi, h1]
      norm_num
    · have hne1 : ¬ (ε i = 1) := by rw [h1]; norm_num
      have hεZi : εZ i = -1 := by
        show (if ε i = 1 then (1 : ℤ) else -1) = -1
        rw [if_neg hne1]
      rw [hεZi, h1]
      norm_num
  have hεZpm : ∀ i : Fin 3, εZ i = 1 ∨ εZ i = -1 := by
    intro i
    by_cases h1 : ε i = 1
    · exact Or.inl (by show (if ε i = 1 then (1 : ℤ) else -1) = 1; rw [if_pos h1])
    · exact Or.inr (by show (if ε i = 1 then (1 : ℤ) else -1) = -1; rw [if_neg h1])
  -- step (9): the value of `χᵢ` at `x`
  have hval9 : ∀ i : Fin 3, χ i x = ε i := by
    intro i
    have h6 : Work.CharCore.cfInner (χ i) h.eta =
        (Nat.card ↥(Hstar x) : ℂ)⁻¹ * ∑ u : ↥(Hstar x), χ i (x * (u : G)) :=
      step6_inner_eta h (hIrr i)
    have hcf2 : Work.CharCore.IsClassFun (χ i ^ 2) := by
      intro g hh
      simp only [Pi.pow_apply]
      rw [Work.CharCore.isClassFun_of_mem_Irr (hIrr i) g hh]
    have h6sq : Work.CharCore.cfInner (χ i ^ 2) h.eta =
        (Nat.card ↥(Hstar x) : ℂ)⁻¹ *
          ∑ u : ↥(Hstar x), (χ i (x * (u : G))) ^ 2 := by
      have hh := step6_inner_eta_classfun h hcf2
      simpa only [Pi.pow_apply] using hh
    have hconjH : ∀ u : G, u ∈ Hstar x → χ i (x * u) = χ i (x * u⁻¹) :=
      fun u hu => step7b_values_conj h (hIrr i) (hint i) hu
    have hηcf : Work.CharCore.cfInner (χ i) h.eta = ε i :=
      cfInner_eta_eq_eps h χ ε hIrr hne hdist hε hη i
    obtain ⟨h8, h8sq⟩ := step8_odd h (χ i) (ε i) (hIrr i) (hε i) hηcf (hint i) hconjH h6 h6sq
    exact step9_chi_x h (hIrr i) (hne i) (hε i) hηcf h6sq (hint i) h8 h8sq (hker_ne i) (hdeg i)
  -- step (10) for each `i`
  have hcong : ∀ i : Fin 3, ∃ Y : ℤ, χ i (x ^ 2) = (Y : ℂ) ∧
      (4 : ℤ) ∣ ((Work.CharCore.irrDeg (χ i) : ℤ) - Y) ∧
      Odd (Work.CharCore.irrDeg (χ i)) ∧
      ((8 : ℤ) ∣ ((Work.CharCore.irrDeg (χ i) : ℤ) - Y) →
        (4 : ℤ) ∣ ((Work.CharCore.irrDeg (χ i) : ℤ) - εZ i)) := by
    intro i
    refine step10_character_congruences S d h2 h.hxS h.hx4 (hIrr i) (εZ i) (hεZpm i) ?_
    intro y hyS hy4
    rw [hεZval i]
    obtain ⟨c, hc⟩ := isConj_iff.mp (hconj y x hy4 h.hx4)
    have hcl := Work.CharCore.isClassFun_of_mem_Irr (hIrr i)
    have hyx : χ i y = χ i x := by
      have h1 := hcl y c
      rw [hc] at h1
      exact h1.symm
    rw [hyx, hval9 i]
  -- the integer data `xᵢ`, `zᵢ` of step (11)
  let Yf : Fin 3 → ℤ := fun i => Classical.choose (hcong i)
  have hYf := fun i => Classical.choose_spec (hcong i)
  let xd : Fin 3 → ℤ := fun i => (Work.CharCore.irrDeg (χ i) : ℤ)
  let zz : Fin 3 → ℤ := fun i => xd i - Yf i
  have hxd : ∀ i : Fin 3, ((xd i : ℤ) : ℂ) = χ i 1 := by
    intro i
    show (((Work.CharCore.irrDeg (χ i) : ℤ)) : ℂ) = χ i 1
    push_cast
    exact (Work.CharCore.irrDeg_spec (hIrr i)).symm
  have hxodd : ∀ i : Fin 3, Odd (xd i) := fun i => by
    show Odd ((Work.CharCore.irrDeg (χ i) : ℤ))
    exact_mod_cast (hYf i).2.2.1
  have hz4 : ∀ i : Fin 3, (4 : ℤ) ∣ zz i := fun i => by
    show (4 : ℤ) ∣ xd i - Yf i
    exact (hYf i).2.1
  have hzc : ∀ i : Fin 3, (zz i : ℂ) = χ i 1 - χ i (x ^ 2) := by
    intro i
    show ((xd i - Yf i : ℤ) : ℂ) = χ i 1 - χ i (x ^ 2)
    push_cast
    rw [hxd i, ← (hYf i).1]
  have hzpos' : ∀ i : Fin 3, 0 < zz i := by
    intro i
    have h1 : (zz i : ℝ) = ((χ i 1 - χ i (x ^ 2) : ℂ)).re := by
      rw [← Complex.intCast_re (zz i), hzc i]
    have h2 := hzpos i
    rw [← h1] at h2
    exact_mod_cast h2
  have h5b1 : 1 + ∑ i : Fin 3, εZ i * xd i = 0 := by
    have hcast : (((1 + ∑ i : Fin 3, εZ i * xd i : ℤ)) : ℂ) = 0 := by
      have h1' : (((1 + ∑ i : Fin 3, εZ i * xd i : ℤ)) : ℂ) =
          (1 : ℂ) + ∑ i : Fin 3, ε i * χ i 1 := by
        push_cast
        refine congrArg (fun t => (1 : ℂ) + t) (Finset.sum_congr rfl ?_)
        intro i _
        rw [hεZval i, hxd i]
      rw [h1', hx1]
    exact_mod_cast hcast
  have hCsum : (∑ i : Fin 3, (εZ i : ℂ) * (zz i : ℂ) ^ 2 / (xd i : ℂ)) = 0 := by
    have h1 : ∀ i : Fin 3, (εZ i : ℂ) * (zz i : ℂ) ^ 2 / (xd i : ℂ) =
        ε i * (χ i 1 - χ i (x ^ 2)) ^ 2 / (χ i 1) := by
      intro i
      rw [hεZval i, hzc i, hxd i]
    rw [Finset.sum_congr rfl (fun i _ => h1 i), hx3z]
  have h5b3 : ∑ i : Fin 3, (εZ i : ℚ) * (zz i : ℚ) ^ 2 / (xd i : ℚ) = 0 := by
    have hcast : (((∑ i : Fin 3, (εZ i : ℚ) * (zz i : ℚ) ^ 2 / (xd i : ℚ) : ℚ)) : ℂ) = 0 := by
      push_cast
      exact hCsum
    exact_mod_cast hcast
  obtain ⟨i, h8z, h8x⟩ := Work.BrauerSuzuki.Arith.glauberman_step11 εZ xd zz hεZpm hxodd
    hzpos' hz4 h5b1 h5b3
  have h4a' : (4 : ℤ) ∣ (xd i - εZ i) := (hYf i).2.2.2 (by simpa only [zz] using h8z)
  have hcon : (4 : ℤ) ∣ 2 * εZ i := by
    have h := dvd_sub h8x h4a'
    have he : xd i + εZ i - (xd i - εZ i) = 2 * εZ i := by ring
    rwa [he] at h
  rcases hεZpm i with h | h <;> rw [h] at hcon <;> norm_num at hcon

/-- **The minimal-counterexample step.**  If `O(G) = ⊥`, `S` is a `Q₈`-Sylow subgroup, the
statement holds in all smaller groups, and `x ∈ S` has order `4`, then `x ^ 2` is central. -/
theorem no_counterexample {G : Type*} [Group G] [Fintype G]
    (hO : Submission.Blueprint.oddCore G = ⊥)
    (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S) (h2 : d.n = 2)
    (x : G) (hxS : x ∈ (S : Subgroup G)) (hx4 : orderOf x = 4)
    (hIH : ∀ (H : Type) [Group H] [Finite H], Nat.card H < Nat.card G →
      ∀ (T : Sylow 2 H) (e : Work.BrauerSuzuki.GenQuaternionData ↥T), e.n = 2 →
      ∀ y : H, y ∈ (T : Subgroup H) → orderOf y = 4 →
      ∀ k : H, y ^ 2 * k * (y ^ 2)⁻¹ * k⁻¹ ∈ Submission.Blueprint.oddCore H)
    (g : G) : x ^ 2 * g * (x ^ 2)⁻¹ * g⁻¹ ∈ Submission.Blueprint.oddCore G := by
  classical
  by_contra hg
  have huniq := hasUniqueInvolution_sylow_of_genQuaternionData S d
  have hx2 : orderOf (x ^ 2) = 2 := sq_orderOf_two hx4
  -- `|Z(G)| ≠ 2`
  have hZ : Nat.card ↥(Subgroup.center G) ≠ 2 := by
    intro hZ2
    have huu := unique_involution_of_card_center_eq_two huniq hZ2
    have hcen : x ^ 2 ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h1 : orderOf (y * x ^ 2 * y⁻¹) = 2 := by
        rw [Work.BrauerSuzuki.Group.orderOf_conj_eq]
        exact hx2
      have h2 : x ^ 2 = y * x ^ 2 * y⁻¹ := huu (x ^ 2) (y * x ^ 2 * y⁻¹) hx2 h1
      have h2' : y * x ^ 2 * y⁻¹ = x ^ 2 := h2.symm
      have h := congrArg (fun t => t * y) h2'
      rwa [mul_assoc, inv_mul_cancel, mul_one] at h
    rw [Subgroup.mem_center_iff] at hcen
    have hcomm : x ^ 2 * g = g * x ^ 2 := (hcen g).symm
    exact hg (by
      rw [hO, Subgroup.mem_bot]
      calc x ^ 2 * g * (x ^ 2)⁻¹ * g⁻¹ = (g * x ^ 2) * (x ^ 2)⁻¹ * g⁻¹ := by rw [hcomm]
        _ = 1 := by group)
  -- all elements of order `4` are conjugate
  have hconj : ∀ y z : G, orderOf y = 4 → orderOf z = 4 → IsConj y z := by
    by_contra hnot
    push_neg at hnot
    obtain ⟨y, z, hy4, hz4, hyz⟩ := hnot
    have hFC := step4b_frobenius S d h2 ⟨y, z, hy4, hz4, hyz⟩
    have hNPC : Work.NPC.HasNormalPComplement 2 G := Work.NPC.frobenius_npc hFC
    exact hZ (step4b_center S d h2 hO hNPC)
  exact character_contradiction S d h2 (ctx_of S d h2 hxS hx4) hO hZ hconj hIH

/-- The statement of the theorem, parameterised by `|G|` so that it can be proved by strong
induction; it is `BrauerSuzukiQ8Strong` with an extra cardinality parameter. -/
def MainStatement (n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Nat.card G = n → ∀ (S : Sylow 2 G)
      (d : Work.BrauerSuzuki.GenQuaternionData ↥S), d.n = 2 →
    ∀ t : G, orderOf t = 2 → ∀ g : G,
      t * g * t⁻¹ * g⁻¹ ∈ Submission.Blueprint.oddCore G

/-- Strong induction on `|G|`: if `O(G) ≠ ⊥` pass to `G ⧸ O(G)`, otherwise use
`no_counterexample`. -/
theorem main_aux : ∀ n : ℕ, MainStatement n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro G _inst _instFin hcard S d h2 t ht g
    classical
    letI : Fintype G := Fintype.ofFinite G
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    by_cases hO : Submission.Blueprint.oddCore G = ⊥
    · -- ## `O(G) = ⊥`: the minimal-counterexample argument
      have hτS : (d.tau : G) ∈ (S : Subgroup G) := d.tau.2
      have hτ4 : orderOf (d.tau : G) = 4 := by
        rw [Subgroup.orderOf_coe, d.tau_order, h2]
        norm_num
      have hIH : ∀ (H : Type) [Group H] [Finite H], Nat.card H < Nat.card G →
          ∀ (T : Sylow 2 H) (e : Work.BrauerSuzuki.GenQuaternionData ↥T), e.n = 2 →
          ∀ y : H, y ∈ (T : Subgroup H) → orderOf y = 4 →
          ∀ k : H, y ^ 2 * k * (y ^ 2)⁻¹ * k⁻¹ ∈ Submission.Blueprint.oddCore H := by
        intro H _ _ hlt T e he y hyS hy4 k
        exact ih (Nat.card H) (hcard ▸ hlt) H rfl T e he (y ^ 2) (sq_orderOf_two hy4) k
      have hcent : ∀ c : G, (d.tau : G) ^ 2 * c * ((d.tau : G) ^ 2)⁻¹ * c⁻¹ ∈
          Submission.Blueprint.oddCore G :=
        fun c => no_counterexample hO S d h2 d.tau hτS hτ4 hIH c
      exact strong_of_central S d h2 hcent t ht g
    · -- ## `O(G) ≠ ⊥`: pass to the quotient by the odd core
      have hKg : Submission.Blueprint.oddCore G ≠ ⊥ := hO
      have hpos : 1 < Nat.card ↥(Submission.Blueprint.oddCore G) := by
        rw [Nat.one_lt_iff_ne_zero_and_ne_one]
        refine ⟨Nat.card_pos.ne', fun h1 => hKg ?_⟩
        exact Subgroup.card_eq_one.mp h1
      have hcardmul : Nat.card ↥(Submission.Blueprint.oddCore G) *
          Nat.card (G ⧸ Submission.Blueprint.oddCore G) = Nat.card G := by
        rw [← Subgroup.index_eq_card, Subgroup.card_mul_index]
      have hlt : Nat.card (G ⧸ Submission.Blueprint.oddCore G) < Nat.card G := by
        have hq : 0 < Nat.card (G ⧸ Submission.Blueprint.oddCore G) := Nat.card_pos
        calc Nat.card (G ⧸ Submission.Blueprint.oddCore G)
            = 1 * Nat.card (G ⧸ Submission.Blueprint.oddCore G) := (one_mul _).symm
          _ < Nat.card ↥(Submission.Blueprint.oddCore G) *
                Nat.card (G ⧸ Submission.Blueprint.oddCore G) :=
              Nat.mul_lt_mul_of_pos_right hpos hq
          _ = Nat.card G := hcardmul
      obtain ⟨T, d', hd'⟩ := Work.BrauerSuzuki.Sylow.genQuaternionData_quotient_oddCore S d h2
      by_cases ht1 : (QuotientGroup.mk' (Submission.Blueprint.oddCore G)) t = 1
      · have hmem : t * g * t⁻¹ * g⁻¹ ∈ Submission.Blueprint.oddCore G := by
          have h1 : (QuotientGroup.mk' (Submission.Blueprint.oddCore G))
              (t * g * t⁻¹ * g⁻¹) = 1 := by
            rw [map_mul, map_mul, map_mul, map_inv, map_inv, ht1]
            group
          have h2 : t * g * t⁻¹ * g⁻¹ ∈
              (QuotientGroup.mk' (Submission.Blueprint.oddCore G)).ker := by
            rwa [MonoidHom.mem_ker]
          rwa [QuotientGroup.ker_mk'] at h2
        exact hmem
      · have htt : t * t = 1 := by
          have h := pow_orderOf_eq_one t
          rw [ht, pow_two] at h
          exact h
        have ht' : orderOf (QuotientGroup.mk' (Submission.Blueprint.oddCore G) t) = 2 := by
          refine orderOf_eq_prime ?_ ht1
          rw [pow_two, ← map_mul, htt, map_one]
        have hres := ih (Nat.card (G ⧸ Submission.Blueprint.oddCore G)) (hcard ▸ hlt)
          (G ⧸ Submission.Blueprint.oddCore G) rfl T d' hd'
          (QuotientGroup.mk' (Submission.Blueprint.oddCore G) t) ht'
          (QuotientGroup.mk' (Submission.Blueprint.oddCore G) g)
        have hres' : (QuotientGroup.mk' (Submission.Blueprint.oddCore G) t) *
            (QuotientGroup.mk' (Submission.Blueprint.oddCore G) g) *
            ((QuotientGroup.mk' (Submission.Blueprint.oddCore G) t))⁻¹ *
            ((QuotientGroup.mk' (Submission.Blueprint.oddCore G) g))⁻¹ = 1 := by
          have h := hres
          rw [Work.ThreePoints.oddCore_quotient_oddCore] at h
          exact Subgroup.mem_bot.mp h
        have h1 : (QuotientGroup.mk' (Submission.Blueprint.oddCore G))
            (t * g * t⁻¹ * g⁻¹) = 1 := by
          rw [map_mul, map_mul, map_mul, map_inv, map_inv]
          exact hres'
        have h2 : t * g * t⁻¹ * g⁻¹ ∈
            (QuotientGroup.mk' (Submission.Blueprint.oddCore G)).ker := by
          rwa [MonoidHom.mem_ker]
        rwa [QuotientGroup.ker_mk'] at h2
end Work.BrauerSuzuki.Q8
