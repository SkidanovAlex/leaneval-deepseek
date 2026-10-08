/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The odd part of the centralizer of an outer involution is trivial

`Work.DSTR.M110.twistCentralOdd`: if `t ∈ PΓL(2,q)` is an involution outside `PGL(2,q)`
(`q = p ^ k`, `p` odd, `q ≥ 5`) and `M ≤ C_{PSL(2,q)}(t)` is an odd-order subgroup normalized
by `C_{PSL(2,q)}(t)`, then `M = 1`.

The mathematical content is the classical fact that the centralizer of a "twist" (field
automorphism type) involution of `PSL(2,q)` is `PGL(2,q₀)` (`q = q₀²`), whose only normal
subgroups are `1`, `PSL(2,q₀)` and itself.  The argument here avoids that structure theory and
is entirely elementary:

* an outer involution of `PΓL(2,q)` is `PΓL`-conjugate to the pure field automorphism
  `galHom σ` (`Work.DSTR.M110.exists_conj_galPart`), so it suffices to treat `t = galHom σ`;
* for `t = galHom σ` the fixed-point set `X = Fix(galHom σ)` of `t` on `ℙ¹(F)` is the set of
  `∞` and the `σ`-fixed elements of `F`; the centralizer `S = C_{PSL}(t)` contains the
  translations `transl c` for `σ c = c` (which act transitively on `X ∖ {∞}`) and the Weyl
  element `weylEl` (which sends `∞` to `0`);
* if some element of `M` moves `∞`, then `M` is transitive on `X`, so `|X| ∣ |M|`; but
  `|X| = |Fix σ| + 1` is even while `|M|` is odd – contradiction;
* if every element of `M` fixes `∞`, then conjugating by the Weyl element shows that every
  element of `M` is a dilation `x ↦ a²x`, while conjugating by `transl 1` forces `a² = 1`.
-/
import Mathlib
import Submission.Work.DSTR.M110.Defs
import Submission.Work.DSTR.M110.Mobius
import Submission.Work.DSTR.M110.Stabilizer
import Submission.Work.DSTR.M110.Galois.decomposition
import Submission.Work.DSTR.M110.SplitCase.GaloisPart
import Submission.Work.DSTR.M110.Normalizer.Defs
import Submission.Work.DSTR.M110.SplitCase.FixedField
import Submission.Work.DSTR.M110.SplitCase.PglCentralizer
import Submission.Work.DSTR.M110.twistOuterInvolutionFixedPoint
import Submission.Work.DSTR.M110.twistAux.twistAuxOrderTwoAffineNorm

open scoped MatrixGroups LinearAlgebra.Projectivization
open OnePoint

namespace Work.DSTR.M110

open Work.AUTL2

/-! ## Elementary conjugation formulae -/

/-- The field automorphism `galHom σ` conjugates the translation `x ↦ x + c` into the
translation `x ↦ x + σ c`. -/
lemma galHom_conj_transl (F : Type*) [Field F] [DecidableEq F] (σ : F ≃+* F) (c : F) :
    galHom F σ * transl F c * (galHom F σ)⁻¹ = transl F (σ c) := by
  have hsig : ((galHom F σ)⁻¹ : Equiv.Perm (P1 F)) = galHom F σ.symm := by
    rw [← map_inv]; rfl
  rw [hsig, Equiv.ext_iff, OnePoint.forall]
  refine ⟨?_, fun x => ?_⟩
  · simp only [Equiv.Perm.mul_apply, Normalizer.galHom_apply_infty, transl_infty]
  · simp only [Equiv.Perm.mul_apply, Normalizer.galHom_apply_coe, transl_formula]
    rw [map_add, RingEquiv.apply_symm_apply]

/-- The field automorphism `galHom σ` fixes the Weyl element `x ↦ -1/x` (its matrix has entries
in the prime field). -/
lemma galHom_conj_weylEl (F : Type*) [Field F] [DecidableEq F] (σ : F ≃+* F) :
    galHom F σ * weylEl F * (galHom F σ)⁻¹ = weylEl F := by
  have hsig : ((galHom F σ)⁻¹ : Equiv.Perm (P1 F)) = galHom F σ.symm := by
    rw [← map_inv]; rfl
  rw [hsig, Equiv.ext_iff, OnePoint.forall]
  refine ⟨?_, fun x => ?_⟩
  · simp only [Equiv.Perm.mul_apply, Normalizer.galHom_apply_infty, weyl_infty,
      Normalizer.galHom_apply_coe, map_zero]
  · rcases eq_or_ne x 0 with rfl | hx
    · simp only [Equiv.Perm.mul_apply, Normalizer.galHom_apply_infty, weyl_infty,
        Normalizer.galHom_apply_coe, map_zero, weyl_zero]
    · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Normalizer.galHom_apply_coe,
        weyl_formula F (σ.symm x) (by simpa using σ.symm.injective.ne hx),
        Normalizer.galHom_apply_coe, weyl_formula F x hx]
      simp only [map_neg, map_inv₀, RingEquiv.apply_symm_apply]

/-- Conjugation by the Weyl element inverts dilations. -/
lemma weylEl_conj_dil (F : Type*) [Field F] [DecidableEq F] (a : Fˣ) :
    weylEl F * dil F a * (weylEl F)⁻¹ = dil F a⁻¹ := by
  have hwinv : (weylEl F)⁻¹ = weylEl F := inv_eq_of_mul_eq_one_right (weyl_self F)
  rw [hwinv, Equiv.ext_iff, OnePoint.forall]
  refine ⟨?_, fun x => ?_⟩
  · simp only [Equiv.Perm.mul_apply, weyl_infty, dil_infty, weyl_zero, dil_formula, mul_zero]
  · rcases eq_or_ne x 0 with rfl | hx
    · simp only [Equiv.Perm.mul_apply, weyl_zero, dil_formula, mul_zero, weyl_infty, dil_infty]
    · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, weyl_formula F x hx, dil_formula,
        weyl_formula F (↑a ^ 2 * -x⁻¹) (by
          exact mul_ne_zero (pow_ne_zero 2 (Units.ne_zero a))
            (neg_ne_zero.mpr (inv_ne_zero hx))),
        dil_formula, Units.val_inv_eq_inv_val]
      congr 1
      have ha : (↑a : F) ≠ 0 := Units.ne_zero a
      field_simp

/-! ## The `galHom σ`-case -/

/-- **The `σ`-case.**  Let `σ` be a field automorphism of a finite field `F`, `M` an odd-order
subgroup of `PSL(2,F)` centralizing `galHom σ` and normalized by `C_{PSL}(galHom σ)`, and
suppose that the fixed field of `σ` has odd cardinality.  Then `M = 1`. -/
theorem centralizerGalHomBot (F : Type*) [Field F] [DecidableEq F] [Finite F]
    (σ : F ≃+* F) (hfixcard : Odd (Nat.card {c : F // σ c = c}))
    (M : Subgroup (Equiv.Perm (P1 F)))
    (hMle : M ≤ pslImage F ⊓ Subgroup.centralizer ({galHom F σ} : Set (Equiv.Perm (P1 F))))
    (hMnorm : ∀ c : Equiv.Perm (P1 F),
      c ∈ pslImage F ⊓ Subgroup.centralizer ({galHom F σ} : Set (Equiv.Perm (P1 F))) →
        ∀ x ∈ M, c * x * c⁻¹ ∈ M)
    (hModd : Odd (Nat.card M)) : M = ⊥ := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  set S : Subgroup (Equiv.Perm (P1 F)) :=
    pslImage F ⊓ Subgroup.centralizer ({galHom F σ} : Set (Equiv.Perm (P1 F))) with hS
  have hMemS : ∀ x : Equiv.Perm (P1 F), x ∈ S ↔ x ∈ pslImage F ∧
      x ∈ Subgroup.centralizer ({galHom F σ} : Set (Equiv.Perm (P1 F))) :=
    fun x => Subgroup.mem_inf
  -- the Weyl element lies in `S`
  have hweylS : weylEl F ∈ S := by
    refine (hMemS _).mpr ⟨weylEl_mem F, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := galHom_conj_weylEl F σ
    have h2 : galHom F σ * weylEl F = weylEl F * galHom F σ := by
      have hh := congrArg (fun t : Equiv.Perm (P1 F) => t * galHom F σ) h
      simpa [mul_assoc] using hh
    exact h2.symm
  -- the translations by `σ`-fixed elements lie in `S`
  have htranslS : ∀ c : F, σ c = c → transl F c ∈ S := by
    intro c hc
    refine (hMemS _).mpr ⟨transl_mem F c, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := galHom_conj_transl F σ c
    rw [hc] at h
    have h2 : galHom F σ * transl F c = transl F c * galHom F σ := by
      have hh := congrArg (fun t : Equiv.Perm (P1 F) => t * galHom F σ) h
      simpa [mul_assoc] using hh
    exact h2.symm
  have hwinv : (weylEl F)⁻¹ = weylEl F := inv_eq_of_mul_eq_one_right (weyl_self F)
  by_cases hfix : ∀ m ∈ M, m (∞ : P1 F) = ∞
  · -- ## Case 1: every element of `M` fixes `∞`
    have hweylconj : ∀ m ∈ M, weylEl F * m * (weylEl F)⁻¹ ∈ M :=
      fun m hm => hMnorm (weylEl F) hweylS m hm
    have hdil1 : ∀ m ∈ M, ∃ a : Fˣ, weylEl F * m * (weylEl F)⁻¹ = dil F a := by
      intro m hm
      have hm' : weylEl F * m * (weylEl F)⁻¹ ∈ M := hweylconj m hm
      have hpsl : weylEl F * m * (weylEl F)⁻¹ ∈ pslImage F := ((hMemS _).mp (hMle hm')).1
      have hinf : (weylEl F * m * (weylEl F)⁻¹) (∞ : P1 F) = ∞ := hfix _ hm'
      have hzero : (weylEl F * m * (weylEl F)⁻¹) ((0 : F) : P1 F) = ((0 : F) : P1 F) := by
        rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hwinv, weyl_zero, hfix m hm, weyl_infty]
      obtain ⟨a, ha⟩ := fixing_infty_zero F _ hpsl hinf hzero
      refine ⟨a, ?_⟩
      rw [Equiv.ext_iff, OnePoint.forall]
      exact ⟨by rw [hinf, dil_infty], fun x => by rw [ha x, dil_formula]⟩
    have hMdil : ∀ m ∈ M, ∃ a : Fˣ, m = dil F a := by
      intro m hm
      obtain ⟨a, ha⟩ := hdil1 m hm
      have h1 : (weylEl F)⁻¹ * (weylEl F * m * (weylEl F)⁻¹) * weylEl F = m := by
        rw [hwinv]
        calc weylEl F * (weylEl F * m * weylEl F) * weylEl F
            = (weylEl F * weylEl F) * m * (weylEl F * weylEl F) := by group
          _ = m := by rw [weyl_self F]; group
      refine ⟨a⁻¹, ?_⟩
      rw [← h1, ha, hwinv]
      simpa [hwinv] using weylEl_conj_dil F a
    refine (Subgroup.eq_bot_iff_forall M).mpr ?_
    intro m hm
    obtain ⟨a, ha⟩ := hMdil m hm
    have hconj : transl F 1 * m * (transl F 1)⁻¹ ∈ M :=
      hMnorm (transl F 1) (htranslS 1 (map_one σ)) m hm
    obtain ⟨b, hb⟩ := hMdil _ hconj
    have h1inv : (transl F 1)⁻¹ = transl F (-1) :=
      inv_eq_of_mul_eq_one_right (by rw [transl_mul, neg_add_cancel, transl_zero])
    have hval : (transl F 1 * m * (transl F 1)⁻¹) ((0 : F) : P1 F) = ((0 : F) : P1 F) := by
      rw [hb, dil_formula, mul_zero]
    have hval' : (transl F 1 * m * (transl F 1)⁻¹) ((0 : F) : P1 F)
        = ((1 - ↑a ^ 2 : F) : P1 F) := by
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h1inv, ha, transl_formula, dil_formula,
        transl_formula]
      congr 1
      ring
    have h1a : (↑a ^ 2 : F) = 1 := by
      have h := hval'.symm.trans hval
      have h2 : (1 - ↑a ^ 2 : F) = 0 := OnePoint.coe_eq_coe.mp h
      exact (sub_eq_zero.mp h2).symm
    have hdilone : dil F a = 1 := by
      rw [Equiv.ext_iff, OnePoint.forall]
      exact ⟨by rw [dil_infty]; exact Equiv.Perm.one_apply _, fun x => by
        rw [dil_formula, h1a, one_mul]; exact Equiv.Perm.one_apply _⟩
    rw [ha, hdilone]
  · -- ## Case 2: some element of `M` moves `∞`
    push_neg at hfix
    obtain ⟨m₀, hm₀M, hm₀ne⟩ := hfix
    letI : MulAction ↥M (P1 F) :=
      { smul := fun m x => (m : Equiv.Perm (P1 F)) x
        one_smul := fun x => rfl
        mul_smul := fun m n x => rfl }
    set Ω : Set (P1 F) := MulAction.orbit ↥M (∞ : P1 F) with hΩ
    have hne : ∃ y ∈ Ω, y ≠ (∞ : P1 F) :=
      ⟨(m₀ : Equiv.Perm (P1 F)) (∞ : P1 F),
        MulAction.mem_orbit (∞ : P1 F) (⟨m₀, hm₀M⟩ : ↥M), hm₀ne⟩
    -- `Ω` consists of `galHom σ`-fixed points
    have hΩX : Ω ⊆ {y : P1 F | galHom F σ y = y} := by
      rintro y ⟨m, rfl⟩
      have hcomm : (m : Equiv.Perm (P1 F)) * galHom F σ =
          galHom F σ * (m : Equiv.Perm (P1 F)) :=
        Subgroup.mem_centralizer_singleton_iff.mp ((hMemS _).mp (hMle m.2)).2
      calc galHom F σ ((m : Equiv.Perm (P1 F)) (∞ : P1 F))
          = (m : Equiv.Perm (P1 F)) (galHom F σ (∞ : P1 F)) := by
            rw [← Equiv.Perm.mul_apply, hcomm.symm, Equiv.Perm.mul_apply]
        _ = (m : Equiv.Perm (P1 F)) (∞ : P1 F) := by rw [Normalizer.galHom_apply_infty]
    -- elements of `S` fixing `∞` preserve `Ω`
    have hSinfΩ : ∀ g : Equiv.Perm (P1 F), g ∈ S → g (∞ : P1 F) = ∞ → ∀ y ∈ Ω, g y ∈ Ω := by
      rintro g hgS hginf y ⟨m, rfl⟩
      refine ⟨⟨g * (m : Equiv.Perm (P1 F)) * g⁻¹, hMnorm g hgS _ m.2⟩, ?_⟩
      have hginv : g⁻¹ (∞ : P1 F) = ∞ := by
        have h : g⁻¹ (g (∞ : P1 F)) = (∞ : P1 F) := by
          have h1 := congrArg (fun t : Equiv.Perm (P1 F) => t (∞ : P1 F)) (inv_mul_cancel g)
          simpa using h1
        rwa [hginf] at h
      show (g * (m : Equiv.Perm (P1 F)) * g⁻¹) (∞ : P1 F)
        = g ((m : Equiv.Perm (P1 F)) (∞ : P1 F))
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hginv]
    -- the stabilizer of `∞` in `S` is transitive on the finite `σ`-fixed points
    have htrans : ∀ y z : P1 F, y ≠ (∞ : P1 F) → z ≠ (∞ : P1 F) →
        galHom F σ y = y → galHom F σ z = z →
        ∃ g ∈ S, g (∞ : P1 F) = ∞ ∧ g y = z := by
      intro y z hyne hzne hy hz
      obtain ⟨c, hc⟩ := OnePoint.ne_infty_iff_exists.mp hyne
      obtain ⟨c', hc'⟩ := OnePoint.ne_infty_iff_exists.mp hzne
      have hcσ : σ c = c := by
        refine OnePoint.coe_eq_coe.mp ?_
        rw [← Normalizer.galHom_apply_coe, hc]
        exact hy
      have hc'σ : σ c' = c' := by
        refine OnePoint.coe_eq_coe.mp ?_
        rw [← Normalizer.galHom_apply_coe, hc']
        exact hz
      refine ⟨transl F (c' - c), htranslS _ ?_, transl_infty F (c' - c), ?_⟩
      · rw [map_sub, hcσ, hc'σ]
      · rw [← hc, ← hc', transl_formula]
        congr 1
        ring
    -- `Ω` is the full fixed set
    have hΩeq : Ω = {y : P1 F | galHom F σ y = y} := by
      refine Set.Subset.antisymm hΩX ?_
      intro y hy
      by_cases hyne : y = (∞ : P1 F)
      · rw [hyne]
        exact MulAction.mem_orbit (∞ : P1 F) (1 : ↥M)
      · obtain ⟨y₀, hy₀Ω, hy₀ne⟩ := hne
        obtain ⟨g, hgS, hginf, hgy⟩ := htrans y₀ y hy₀ne hyne (hΩX hy₀Ω) hy
        have := hSinfΩ g hgS hginf y₀ hy₀Ω
        rwa [hgy] at this
    -- cardinality of the fixed set
    have hcardΩ : Nat.card ↥Ω = Nat.card {c : F // σ c = c} + 1 := by
      have heq : Nat.card ↥Ω = Nat.card ↥({y : P1 F | galHom F σ y = y} : Set (P1 F)) := by
        rw [hΩeq]
      rw [heq]
      have hcoe : ∀ c : F, (((c : P1 F)) ∈ ({y : P1 F | galHom F σ y = y} : Set (P1 F)))
          ↔ (σ c = c) := by
        intro c
        have h1 : (((c : P1 F)) ∈ ({y : P1 F | galHom F σ y = y} : Set (P1 F)))
            = (galHom F σ ((c : F) : P1 F) = ((c : F) : P1 F)) := rfl
        rw [h1]
        constructor
        · intro hc
          exact OnePoint.coe_eq_coe.mp (by rw [← Normalizer.galHom_apply_coe]; exact hc)
        · intro hc
          rw [Normalizer.galHom_apply_coe, hc]
      have he : ({y : P1 F // galHom F σ y = y} : Type _) ≃
          ({c : F // σ c = c} ⊕ Fin 1) :=
        { toFun := fun y => if h : (y : P1 F) = (∞ : P1 F) then Sum.inr 0
            else Sum.inl ⟨Classical.choose (OnePoint.ne_infty_iff_exists.mp h),
              (by
                have hch : (((Classical.choose (OnePoint.ne_infty_iff_exists.mp h)) : F) : P1 F)
                    = (y : P1 F) := Classical.choose_spec (OnePoint.ne_infty_iff_exists.mp h)
                have hfix : galHom F σ ((y : P1 F)) = (y : P1 F) := y.2
                refine OnePoint.coe_eq_coe.mp ?_
                calc (((σ (Classical.choose (OnePoint.ne_infty_iff_exists.mp h)) : F) : P1 F))
                    = galHom F σ (((Classical.choose (OnePoint.ne_infty_iff_exists.mp h)) : F) : P1 F) :=
                      (Normalizer.galHom_apply_coe F σ _).symm
                  _ = galHom F σ ((y : P1 F)) := by rw [hch]
                  _ = (y : P1 F) := hfix
                  _ = (((Classical.choose (OnePoint.ne_infty_iff_exists.mp h)) : F) : P1 F) := hch.symm)⟩
          invFun := fun z => match z with
            | Sum.inl c => ⟨((c : F) : P1 F), (hcoe c).mpr c.2⟩
            | Sum.inr _ => ⟨(∞ : P1 F), Normalizer.galHom_apply_infty F σ⟩
          left_inv := by
            intro y
            by_cases h : (y : P1 F) = (∞ : P1 F)
            · simp only [dif_pos h]
              exact Subtype.ext h.symm
            · simp only [dif_neg h]
              exact Subtype.ext (Classical.choose_spec (OnePoint.ne_infty_iff_exists.mp h))
          right_inv := by
            intro z
            match z with
            | Sum.inl c =>
                simp only [dif_neg (OnePoint.coe_ne_infty ((c : F)))]
                congr 1
                exact Subtype.ext (OnePoint.coe_eq_coe.mp (Classical.choose_spec
                  (OnePoint.ne_infty_iff_exists.mp (OnePoint.coe_ne_infty ((c : F))))))
            | Sum.inr n =>
                simp only [dif_pos rfl]
                exact congrArg Sum.inr (Subsingleton.elim (0 : Fin 1) n) }
      rw [show Nat.card ↥({y : P1 F | galHom F σ y = y} : Set (P1 F))
        = Nat.card ({c : F // σ c = c} ⊕ Fin 1) from Nat.card_congr he]
      rw [Nat.card_sum, Nat.card_fin]
    -- `|Ω|` divides `|M|`
    have hdvd : Nat.card ↥Ω ∣ Nat.card ↥M := by
      haveI : Fintype ↥M := Fintype.ofFinite _
      haveI : Fintype ↥(MulAction.orbit ↥M (∞ : P1 F)) := Fintype.ofFinite _
      haveI : Fintype ↥(MulAction.stabilizer ↥M (∞ : P1 F)) := Fintype.ofFinite _
      rw [hΩ, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
      exact ⟨_, (MulAction.card_orbit_mul_card_stabilizer_eq_card_group (↥M) (∞ : P1 F)).symm⟩
    -- contradiction: `|Ω|` is even but `|M|` is odd
    have hoddΩ : Odd (Nat.card ↥Ω) := Odd.of_dvd_nat hModd hdvd
    rw [hcardΩ] at hoddΩ
    obtain ⟨n, hn⟩ := hfixcard
    rw [hn] at hoddΩ
    obtain ⟨m', hm'⟩ := hoddΩ
    omega

/-! ## Conjugating an outer involution to a pure field automorphism -/

/-- **Hilbert 90 step.**  If `σ` is an involutive field automorphism (`σ ≠ 1`) and `a * σ a = 1`,
then `a = σ μ / μ` for some `μ ≠ 0`. -/
lemma exists_sigma_mul_eq_of_mul_sigma_eq_one {F : Type*} [Field F] (σ : F ≃+* F)
    (hσ2 : ∀ x : F, σ (σ x) = x) (hσ1 : σ ≠ 1) {a : F} (ha : a * σ a = 1) :
    ∃ μ : F, μ ≠ 0 ∧ σ μ = μ * a := by
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, zero_mul] at ha
    exact one_ne_zero ha.symm
  by_cases h1 : a + 1 = 0
  · have haeq : a = -1 := (add_eq_zero_iff_eq_neg).mp h1
    obtain ⟨x, hx⟩ : ∃ x : F, σ x ≠ x := by
      by_contra hc
      push Not at hc
      exact hσ1 (by ext x; exact hc x)
    refine ⟨x - σ x, sub_ne_zero.mpr (Ne.symm hx), ?_⟩
    rw [map_sub, hσ2 x, haeq, mul_neg, mul_one]
    ring
  · refine ⟨(a + 1)⁻¹, inv_ne_zero h1, ?_⟩
    have hsa : σ a = a⁻¹ := (inv_eq_of_mul_eq_one_right ha).symm
    rw [map_inv₀, map_add, map_one, hsa]
    have h1' : (1 + a : F) ≠ 0 := by
      intro hh
      exact h1 (by linear_combination hh)
    field_simp
    ring

/-- **The affine form of an element of `PΓL(2,F)` fixing `∞`.** -/
lemma affine_form_of_fixes_infty (F : Type*) [Field F] [DecidableEq F]
    (t : Equiv.Perm (P1 F)) (htG : t ∈ pgammaL F) (htinf : t (∞ : P1 F) = ∞) :
    ∃ (σ : F ≃+* F) (a b : F), σ = SplitAux.galPart F ⟨t, htG⟩ ∧ a ≠ 0 ∧
      (∀ z : F, t (z : P1 F) = ((a * σ z + b : F) : P1 F)) := by
  obtain ⟨c, hc, hcspec⟩ := SplitAux.galPart_spec F ⟨t, htG⟩
  have hcinf : c (∞ : P1 F) = ∞ := by
    have h := congrArg (fun z : Equiv.Perm (P1 F) => z (∞ : P1 F)) hcspec
    rw [Equiv.Perm.mul_apply, Normalizer.galHom_apply_infty, htinf] at h
    exact h.symm
  obtain ⟨a, b, ha, hab⟩ := SplitAux.pglImage_fixing_infty F c hc hcinf
  refine ⟨SplitAux.galPart F ⟨t, htG⟩, a, b, rfl, ha, fun z => ?_⟩
  have h := congrArg (fun w : Equiv.Perm (P1 F) => w (z : P1 F)) hcspec
  rw [Equiv.Perm.mul_apply, Normalizer.galHom_apply_coe, hab] at h
  exact h

/-- **Reduction.**  An outer involution of `PΓL(2,q)` is conjugate, by an element of `PΓL(2,q)`,
to the field automorphism `galHom (galPart t)`. -/
theorem exists_conj_galPart (p k : ℕ) [Fact p.Prime] (hp : Odd p) (hq : 5 ≤ p ^ k)
    [DecidableEq (GaloisField p k)] (t : Equiv.Perm (P1 (GaloisField p k)))
    (htG : t ∈ pgammaL (GaloisField p k)) (ht2 : orderOf t = 2)
    (htnpgl : t ∉ pglImage (GaloisField p k)) :
    ∃ g ∈ pgammaL (GaloisField p k),
      g * t * g⁻¹ = galHom (GaloisField p k) (SplitAux.galPart (GaloisField p k) ⟨t, htG⟩) := by
  classical
  haveI : Fintype (GaloisField p k) := Fintype.ofFinite _
  have h2ne : (2 : GaloisField p k) ≠ 0 := by
    intro h
    have hd : p ∣ 2 := (CharP.cast_eq_zero_iff (GaloisField p k) p 2).mp h
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hd
    have hge : 2 ≤ p := (Fact.out : p.Prime).two_le
    obtain ⟨m, hm⟩ := hp
    omega
  set σ : GaloisField p k ≃+* GaloisField p k :=
    SplitAux.galPart (GaloisField p k) ⟨t, htG⟩ with hσdef
  have ht2' : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rwa [ht2, pow_two] at h
  have hσmul : σ * σ = 1 := by
    have h := SplitAux.galPart_mul (GaloisField p k) ⟨t, htG⟩ ⟨t, htG⟩
    have h1 : (⟨t, htG⟩ * ⟨t, htG⟩ : ↥(pgammaL (GaloisField p k))) = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_one]
      exact ht2'
    rw [h1, SplitAux.galPart_one] at h
    exact h.symm
  have hσ2 : ∀ x : GaloisField p k, σ (σ x) = x := fun x => by
    have h := congrFun (congrArg DFunLike.coe hσmul) x
    simpa using h
  have hσ1 : σ ≠ 1 := by
    intro h
    exact htnpgl ((SplitAux.galPart_eq_one_iff (GaloisField p k) ⟨t, htG⟩).mp h)
  -- step 1: move a fixed point of `t` to `∞`
  obtain ⟨y, hy⟩ := twistOuterInvolutionFixedPoint p k hp hq t htG ht2 htnpgl
  obtain ⟨g₁, hg₁S, hg₁y⟩ := Work.AUTL2.exists_pslImage_map_to_infty (F := GaloisField p k) y
  have hg₁P : g₁ ∈ pglImage (GaloisField p k) := pslImage_le_pglImage _ hg₁S
  have hg₁G : g₁ ∈ pgammaL (GaloisField p k) := Subgroup.mem_sup_left hg₁P
  have hg₁invS : g₁⁻¹ ∈ pslImage (GaloisField p k) := Subgroup.inv_mem _ hg₁S
  have hg₁invP : g₁⁻¹ ∈ pglImage (GaloisField p k) := pslImage_le_pglImage _ hg₁invS
  have hg₁invG : g₁⁻¹ ∈ pgammaL (GaloisField p k) := Subgroup.mem_sup_left hg₁invP
  have hg₁inv_infty : g₁⁻¹ (∞ : P1 (GaloisField p k)) = y := by
    have h : g₁⁻¹ (g₁ y) = g₁⁻¹ (∞ : P1 (GaloisField p k)) := congrArg (fun z => g₁⁻¹ z) hg₁y
    rw [← Equiv.Perm.mul_apply, inv_mul_cancel] at h
    simpa using h.symm
  set t₁ : Equiv.Perm (P1 (GaloisField p k)) := g₁ * t * g₁⁻¹ with ht₁def
  have ht₁inf : t₁ (∞ : P1 (GaloisField p k)) = ∞ := by
    rw [ht₁def, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hg₁inv_infty, hy, hg₁y]
  have ht₁sq : t₁ * t₁ = 1 := by
    rw [ht₁def]
    calc (g₁ * t * g₁⁻¹) * (g₁ * t * g₁⁻¹) = g₁ * (t * t) * g₁⁻¹ := by group
      _ = 1 := by rw [ht2']; group
  have ht₁G : t₁ ∈ pgammaL (GaloisField p k) := by
    rw [ht₁def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg₁G htG) hg₁invG
  have hgal_t₁ : SplitAux.galPart (GaloisField p k) ⟨t₁, ht₁G⟩ = σ := by
    have heq : (⟨t₁, ht₁G⟩ : ↥(pgammaL (GaloisField p k)))
        = ⟨g₁, hg₁G⟩ * ⟨t, htG⟩ * ⟨g₁, hg₁G⟩⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact ht₁def
    rw [heq, SplitAux.galPart_mul, SplitAux.galPart_mul]
    have hg1 : SplitAux.galPart (GaloisField p k) ⟨g₁, hg₁G⟩ = 1 :=
      SplitAux.galPart_of_mem (GaloisField p k) ⟨g₁, hg₁G⟩ hg₁P
    have hg1' : SplitAux.galPart (GaloisField p k) (⟨g₁, hg₁G⟩⁻¹) = 1 :=
      SplitAux.galPart_of_mem (GaloisField p k) _ (Subgroup.inv_mem _ hg₁P)
    rw [hg1, hg1', one_mul, mul_one]
  -- step 2: the affine description of `t₁`
  obtain ⟨σ₁, a, b, hσ₁eq, ha0, hformσ⟩ :=
    affine_form_of_fixes_infty (GaloisField p k) t₁ ht₁G ht₁inf
  have hσ₁ : σ₁ = σ := by rw [hσ₁eq, hgal_t₁]
  have hab : ∀ z : GaloisField p k, t₁ (z : P1 (GaloisField p k))
      = ((a * σ z + b : GaloisField p k) : P1 (GaloisField p k)) := by
    intro z
    rw [← hσ₁]
    exact hformσ z
  have hanorm : a * σ a = 1 :=
    twistAux.twistAuxOrderTwoAffineNorm (GaloisField p k) σ a b t₁ hab ht₁sq
  have hbnorm : a * σ b + b = 0 := by
    have hiter : ∀ z : GaloisField p k, a * σ (a * σ z + b) + b = z := by
      intro z
      have h := congrArg (fun w : Equiv.Perm (P1 (GaloisField p k)) =>
        w (z : P1 (GaloisField p k))) ht₁sq
      rw [Equiv.Perm.mul_apply, Equiv.Perm.one_apply, hab z, hab (a * σ z + b)] at h
      exact OnePoint.coe_eq_coe.mp h
    have h0 := hiter 0
    exact OnePoint.coe_eq_coe.mp (by simpa using h0)
  -- step 3: conjugate by `transl d` with `d = -(2⁻¹) * b`
  set d : GaloisField p k := -(2 : GaloisField p k)⁻¹ * b with hddef
  have hdkey : b + d - a * σ d = 0 := by
    have hσd : σ d = -(2 : GaloisField p k)⁻¹ * σ b := by
      rw [hddef, map_mul, map_neg, map_inv₀, map_ofNat]
    have hab' : a * σ b = -b := by linear_combination hbnorm
    rw [hσd, hddef, show a * (-(2 : GaloisField p k)⁻¹ * σ b)
      = -(2 : GaloisField p k)⁻¹ * (a * σ b) by ring, hab']
    field_simp
    ring
  have htranslinv : (transl (GaloisField p k) d)⁻¹ = transl (GaloisField p k) (-d) :=
    inv_eq_of_mul_eq_one_right (by rw [transl_mul, neg_add_cancel, transl_zero])
  set t₂ : Equiv.Perm (P1 (GaloisField p k)) :=
    transl (GaloisField p k) d * t₁ * (transl (GaloisField p k) d)⁻¹ with ht₂def
  have ht₂form : ∀ z : GaloisField p k,
      t₂ (z : P1 (GaloisField p k)) = ((a * σ z : GaloisField p k) : P1 (GaloisField p k)) := by
    intro z
    rw [ht₂def, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, htranslinv, transl_formula,
      hab, transl_formula]
    congr 1
    rw [show z + -d = z - d from (sub_eq_add_neg z d).symm, map_sub]
    linear_combination hdkey
  have ht₂inf : t₂ (∞ : P1 (GaloisField p k)) = ∞ := by
    rw [ht₂def, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, htranslinv, transl_infty, ht₁inf,
      transl_infty]
  -- step 4: conjugate by `z ↦ μ z` with `σ μ = μ * a`
  obtain ⟨μ, hμ0, hμeq⟩ := exists_sigma_mul_eq_of_mul_sigma_eq_one σ hσ2 hσ1 hanorm
  have ha0' : a ≠ 0 := by
    intro h
    rw [h, zero_mul] at hanorm
    exact one_ne_zero hanorm.symm
  have hμkey : μ * a * (σ μ)⁻¹ = 1 := by
    rw [hμeq, mul_inv_cancel₀ (mul_ne_zero hμ0 ha0')]
  set s : Equiv.Perm (P1 (GaloisField p k)) :=
    Normalizer.smulPerm (GaloisField p k) μ hμ0 with hsdef
  have hsinv : s⁻¹ = Normalizer.smulPerm (GaloisField p k) μ⁻¹ (inv_ne_zero hμ0) :=
    inv_eq_of_mul_eq_one_right (by
      rw [hsdef, Equiv.ext_iff, OnePoint.forall]
      refine ⟨?_, fun z => ?_⟩
      · rw [Equiv.Perm.mul_apply, Normalizer.smulPerm_infty, Normalizer.smulPerm_infty,
          Equiv.Perm.one_apply]
      · rw [Equiv.Perm.mul_apply, Normalizer.smulPerm_some, Normalizer.smulPerm_some,
          Equiv.Perm.one_apply]
        congr 1
        rw [← mul_assoc, mul_inv_cancel₀ hμ0, one_mul])
  have hsinv_apply : ∀ z : GaloisField p k,
      s⁻¹ (z : P1 (GaloisField p k)) = ((μ⁻¹ * z : GaloisField p k) : P1 (GaloisField p k)) := by
    intro z
    rw [hsinv, Normalizer.smulPerm_some]
  have hsinv_infty : s⁻¹ (∞ : P1 (GaloisField p k)) = ∞ := by
    rw [hsinv, Normalizer.smulPerm_infty]
  have hsinf : s (∞ : P1 (GaloisField p k)) = ∞ := by
    rw [hsdef, Normalizer.smulPerm_infty]
  set t₃ : Equiv.Perm (P1 (GaloisField p k)) := s * t₂ * s⁻¹ with ht₃def
  have ht₃form : ∀ z : GaloisField p k,
      t₃ (z : P1 (GaloisField p k)) = ((σ z : GaloisField p k) : P1 (GaloisField p k)) := by
    intro z
    rw [ht₃def, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hsinv_apply, ht₂form, map_mul,
      map_inv₀, hsdef, Normalizer.smulPerm_some]
    congr 1
    calc μ * (a * ((σ μ)⁻¹ * σ z)) = (μ * a * (σ μ)⁻¹) * σ z := by ring
      _ = σ z := by rw [hμkey, one_mul]
  have ht₃inf : t₃ (∞ : P1 (GaloisField p k)) = ∞ := by
    rw [ht₃def, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hsinv_infty, ht₂inf, hsinf]
  have ht₃eq : t₃ = galHom (GaloisField p k) σ := by
    rw [Equiv.ext_iff, OnePoint.forall]
    refine ⟨?_, fun z => ?_⟩
    · rw [ht₃inf, Normalizer.galHom_apply_infty]
    · rw [ht₃form z, Normalizer.galHom_apply_coe]
  refine ⟨s * transl (GaloisField p k) d * g₁, ?_, ?_⟩
  · refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) hg₁G
    · rw [hsdef]
      exact Subgroup.mem_sup_left (Normalizer.smulPerm_mem_pglImage _ _ _)
    · exact Subgroup.mem_sup_left (pslImage_le_pglImage _ (transl_mem _ d))
  · have hkey : (s * transl (GaloisField p k) d * g₁) * t * (s * transl (GaloisField p k) d * g₁)⁻¹
        = t₃ := by
      rw [ht₃def, ht₂def, ht₁def]
      group
    rw [hkey, ht₃eq]

theorem twistCentralOdd (p k : ℕ) [Fact p.Prime] (hp : Odd p) (hq : 5 ≤ p ^ k)
    [DecidableEq (GaloisField p k)] (t : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)))
    (htG : t ∈ Work.AUTL2.pgammaL (GaloisField p k))
    (ht2 : orderOf t = 2) (htnpgl : t ∉ Work.AUTL2.pglImage (GaloisField p k))
    (M : Subgroup (Equiv.Perm (Work.AUTL2.P1 (GaloisField p k))))
    (hMle : M ≤ Work.AUTL2.pslImage (GaloisField p k) ⊓
      Subgroup.centralizer ({t} : Set (Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)))))
    (hMnorm : ∀ c : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)),
      c ∈ Work.AUTL2.pslImage (GaloisField p k) ⊓
        Subgroup.centralizer ({t} : Set (Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)))) →
      ∀ x ∈ M, c * x * c⁻¹ ∈ M)
    (hModd : Odd (Nat.card M)) : M = ⊥ := by
  classical
  -- conjugate the outer involution to a pure field automorphism
  obtain ⟨g, hgG, hgt⟩ := exists_conj_galPart p k hp hq t htG ht2 htnpgl
  haveI : Fintype (GaloisField p k) := Fintype.ofFinite _
  have hk : k ≠ 0 := by rintro rfl; simp at hq
  set σ : GaloisField p k ≃+* GaloisField p k :=
    SplitAux.galPart (GaloisField p k) ⟨t, htG⟩ with hσ
  have ht2' : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rwa [ht2, pow_two] at h
  have hσsq : σ * σ = 1 := by
    have h := SplitAux.galPart_mul (GaloisField p k) ⟨t, htG⟩ ⟨t, htG⟩
    have h1 : (⟨t, htG⟩ * ⟨t, htG⟩ : ↥(pgammaL (GaloisField p k))) = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_one]
      exact ht2'
    rw [h1, SplitAux.galPart_one] at h
    exact h.symm
  have hσ1 : σ ≠ 1 := by
    intro h
    exact htnpgl ((SplitAux.galPart_eq_one_iff (GaloisField p k) ⟨t, htG⟩).mp h)
  have hfixcard : Odd (Nat.card {c : GaloisField p k // σ c = c}) := by
    have hσord : orderOf σ = 2 := orderOf_eq_prime hσsq hσ1
    rw [SplitCase.card_fixed_of_orderOf_eq p k 2 hk Nat.prime_two σ hσord]
    exact hp.pow
  -- conjugate `M` by `g`
  set M' : Subgroup (Equiv.Perm (P1 (GaloisField p k))) :=
    M.map (MulAut.conj g).toMonoidHom with hM'def
  have hgapply : ∀ x : Equiv.Perm (P1 (GaloisField p k)),
      (MulEquiv.toMonoidHom (MulAut.conj g)) x = g * x * g⁻¹ :=
    fun x => MulAut.conj_apply g x
  have hM'le : M' ≤ pslImage (GaloisField p k) ⊓
      Subgroup.centralizer ({galHom (GaloisField p k) σ} :
        Set (Equiv.Perm (P1 (GaloisField p k)))) := by
    intro x hx
    obtain ⟨m, hmM, rfl⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact (Subgroup.le_normalizer_iff.mp
        (Galois.pgammaL_le_normalizer_pslImage (GaloisField p k)) g hgG m (hMle hmM).1)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      have hmt : m * t = t * m := Subgroup.mem_centralizer_singleton_iff.mp (hMle hmM).2
      show (MulEquiv.toMonoidHom (MulAut.conj g)) m * galHom (GaloisField p k) σ
        = galHom (GaloisField p k) σ * (MulEquiv.toMonoidHom (MulAut.conj g)) m
      rw [← hgt]
      show (MulEquiv.toMonoidHom (MulAut.conj g)) m * (g * t * g⁻¹)
        = (g * t * g⁻¹) * (MulEquiv.toMonoidHom (MulAut.conj g)) m
      rw [hgapply m]
      calc g * m * g⁻¹ * (g * t * g⁻¹) = g * (m * t) * g⁻¹ := by group
        _ = g * (t * m) * g⁻¹ := by rw [hmt]
        _ = (g * t * g⁻¹) * (g * m * g⁻¹) := by group
  have hM'norm : ∀ c : Equiv.Perm (P1 (GaloisField p k)),
      c ∈ pslImage (GaloisField p k) ⊓
        Subgroup.centralizer ({galHom (GaloisField p k) σ} :
          Set (Equiv.Perm (P1 (GaloisField p k)))) →
      ∀ x ∈ M', c * x * c⁻¹ ∈ M' := by
    intro c hc x hx
    obtain ⟨m, hmM, rfl⟩ := Subgroup.mem_map.mp hx
    have hginvG : g⁻¹ ∈ pgammaL (GaloisField p k) := Subgroup.inv_mem _ hgG
    have hc0 : g⁻¹ * c * g ∈ pslImage (GaloisField p k) ⊓
        Subgroup.centralizer ({t} : Set (Equiv.Perm (P1 (GaloisField p k)))) := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact (Subgroup.le_normalizer_iff.mp
          (Galois.pgammaL_le_normalizer_pslImage (GaloisField p k)) g⁻¹ hginvG c hc.1)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        have hc' : c * galHom (GaloisField p k) σ = galHom (GaloisField p k) σ * c :=
          Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hc).2
        rw [← hgt] at hc'
        calc g⁻¹ * c * g * t = g⁻¹ * (c * (g * t * g⁻¹)) * g := by group
          _ = g⁻¹ * ((g * t * g⁻¹) * c) * g := by rw [hc']
          _ = t * (g⁻¹ * c * g) := by group
    refine Subgroup.mem_map.mpr ⟨(g⁻¹ * c * g) * m * (g⁻¹ * c * g)⁻¹,
      hMnorm _ hc0 m hmM, ?_⟩
    rw [hgapply, hgapply]
    group
  have hM'odd : Odd (Nat.card M') := by
    rw [hM'def, Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hModd
  have hM'bot : M' = ⊥ := centralizerGalHomBot (GaloisField p k) σ hfixcard M' hM'le hM'norm
    hM'odd
  rw [Subgroup.eq_bot_iff_forall] at hM'bot ⊢
  intro m hm
  have hmem : g * m * g⁻¹ ∈ M' := by
    rw [hM'def]
    exact Subgroup.mem_map.mpr ⟨m, hm, hgapply m⟩
  have h1 : g * m * g⁻¹ = 1 := hM'bot _ hmem
  calc m = g⁻¹ * (g * m * g⁻¹) * g := by group
    _ = 1 := by rw [h1]; group

end Work.DSTR.M110
