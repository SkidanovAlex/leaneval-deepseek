import Mathlib
import Submission.Work.ShafarevichKoch.Bockstein.SES
import Submission.Work.ShafarevichKoch.CountZ
import Submission.Work.ShafarevichKoch.RatCoeff
import Submission.Work.ShafarevichKoch.RatVanishing.subsingleton_H1_H2_rat
import Submission.Work.ConCohomology.Connecting
import Submission.Work.ShafarevichKoch.Cohomology3

/-!
# `Work.ShafarevichKoch.Bockstein.twoTorsionH3_natCard_eq_quot_bockstein`

The `2`-torsion of `H³(G,ℤ)` as the cokernel of the Bockstein connecting map
`δ¹ : H¹(G,ℚ/ℤ) → H²(G,ℤ/2)` attached to the coefficient sequence
`0 → μ₂ → ℚ/ℤ →² ℚ/ℤ → 0` (`Work.ShafarevichKoch.Bockstein.muTwoSES`).

## The mathematics

Write `A = H¹(G,ℚ/ℤ)`, `B₂ = H²(G,ℤ/2)`, `B = H²(G,ℚ/ℤ)`, `C = H³(G,ℤ)`.

* The long exact sequence of `0 → μ₂ → ℚ/ℤ →² ℚ/ℤ → 0` gives
  `im(δ¹) = ker(H²(μ₂) → H²(ℚ/ℤ))` and `im(H²(μ₂) → H²(ℚ/ℤ)) = B[2]`, whence
  `B₂/im(δ¹) ≅ B[2]`.
* The long exact sequence of `0 → ℤ → ℚ → ℚ/ℤ → 0` gives, since `H²(G,ℤ)` is finite
  (`hfin2`) and `H²(G,ℚ)` is torsion-free, that the coefficient map `H²(G,ℤ) → H²(G,ℚ)`
  vanishes, so that `H²(G,ℚ) → H²(G,ℚ/ℤ)` is injective; its image is therefore torsion-free.
  Together with the torsion-freeness of `H³(G,ℚ)` this shows that the connecting map
  `δ₂ : H²(G,ℚ/ℤ) → H³(G,ℤ)` restricts to a bijection `B[2] → C[2] = (H³(G,ℤ))[2]`.

Composing the two bijections gives `#(H³(G,ℤ)[2]) = #(B₂/im δ¹)`, which is the statement.

The two auxiliary facts about `ℚ`-coefficients (torsion-freeness of `H²` and `H³`, and
divisibility of `H²`) are proved directly on cochains, by dividing a cochain (or the
witness of a coboundary) by `n ≠ 0`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open scoped Classical

noncomputable section

namespace Work.ShafarevichKoch.Bockstein

open Work.ConCohomology

section Aux

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-! ### Multiplying `ℚ`-valued cochains by a rational constant -/

/-- Multiplication of a `ℚ`-valued `1`-cochain by a constant commutes with `d¹`
(the action on `ℚ` being trivial). -/
lemma d1Fun_const_mul (u : G → ℚ) (a : ℚ) :
    d1Fun (fun σ => a * u σ) = fun p : G × G => a * d1Fun u p := by
  funext p
  obtain ⟨σ, τ⟩ := p
  have htriv : ∀ (σ : G) (q : ℚ), σ • q = q := fun _ _ => rfl
  simp only [d1Fun_apply]
  rw [htriv σ (a * u τ), htriv σ (u τ)]
  ring

/-- Multiplication of a `ℚ`-valued `2`-cochain by a constant commutes with `d²`. -/
lemma d2Fun_const_mul (u : G × G → ℚ) (a : ℚ) :
    d2Fun (fun p => a * u p) = fun p : G × G × G => a * d2Fun u p := by
  funext p
  obtain ⟨σ, τ, ρ⟩ := p
  have htriv : ∀ (σ : G) (q : ℚ), σ • q = q := fun _ _ => rfl
  simp only [d2Fun_apply]
  rw [htriv σ (a * u (τ, ρ)), htriv σ (u (τ, ρ))]
  ring

/-! ### Coefficient change by `n • ·` -/

/-- A coefficient endomorphism of the shape `m ↦ n • m` induces multiplication by `n` on `H²`. -/
theorem H2Map_eq_nsmul_of_apply_eq {M : Type*} [AddCommGroup M] [DistribMulAction G M]
    [IsDiscreteGModule G M] (n : ℕ) (F : EqHom G M M) (hF : ∀ m : M, F m = n • m)
    (y : H2 G M) : H2Map F y = n • y := by
  refine QuotientAddGroup.induction_on y ?_
  intro z
  show H2Map F (H2.mk z) = n • (H2.mk z : H2 G M)
  rw [H2Map_mk]
  have h : Z2Map F z = n • z := by
    apply Subtype.ext
    refine LocallyConstant.ext fun p => ?_
    show F ((z : Cochain2 G M) p) = ((n • z : Z2 G M) : Cochain2 G M) p
    rw [hF]
    rfl
  rw [h]
  exact map_nsmul (QuotientAddGroup.mk' (B2' G M)) n z

/-! ### The `ℚ`-cohomology of a `2`-cocycle -/

/-- `H²(G,ℚ)` is divisible: every class is `n` times a class, for `n ≠ 0`. -/
theorem exists_nsmul_eq_H2_rat (n : ℕ) (hn : n ≠ 0) (w : H2 G ℚ) :
    ∃ w' : H2 G ℚ, n • w' = w := by
  have hnQ : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  refine QuotientAddGroup.induction_on w ?_
  intro ζ
  have hcyc : IsCocycle2 (fun p : G × G => (1 / (n : ℚ)) * (ζ : Cochain2 G ℚ) p) := by
    rw [isCocycle2_iff_d2Fun, d2Fun_const_mul]
    rw [(isCocycle2_iff_d2Fun _).mp (mem_Z2.mp ζ.2)]
    funext p
    simp
  let ζ' : Z2 G ℚ :=
    ⟨⟨fun p : G × G => (1 / (n : ℚ)) * (ζ : Cochain2 G ℚ) p,
        (ζ : Cochain2 G ℚ).isLocallyConstant.comp (fun q => (1 / (n : ℚ)) * q)⟩,
      mem_Z2.mpr hcyc⟩
  refine ⟨H2.mk ζ', ?_⟩
  have hζ' : n • ζ' = ζ := by
    apply Subtype.ext
    refine LocallyConstant.ext fun p => ?_
    show ((n • ζ' : Z2 G ℚ) : Cochain2 G ℚ) p = (ζ : Cochain2 G ℚ) p
    rw [AddSubgroup.coe_nsmul]
    show n • ((ζ' : Cochain2 G ℚ) p) = (ζ : Cochain2 G ℚ) p
    show n • ((1 / (n : ℚ)) * (ζ : Cochain2 G ℚ) p) = (ζ : Cochain2 G ℚ) p
    rw [nsmul_eq_mul, ← mul_assoc, one_div, mul_inv_cancel₀ hnQ, one_mul]
  calc n • H2.mk ζ' = H2.mk (n • ζ') :=
        (map_nsmul (QuotientAddGroup.mk' (B2' G ℚ)) n ζ').symm
    _ = H2.mk ζ := by rw [hζ']

/-- `H²(G,ℚ)` has no torsion: a class killed by `n ≠ 0` vanishes. -/
theorem H2_rat_eq_zero_of_nsmul_eq_zero (n : ℕ) (hn : n ≠ 0) {z : H2 G ℚ}
    (hz : n • z = 0) : z = 0 := by
  have hnQ : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hmain : ∀ w : H2 G ℚ, n • w = 0 → w = 0 := by
    intro w
    refine QuotientAddGroup.induction_on w ?_
    intro ζ hw
    change H2.mk ζ = 0
    rw [H2.mk_eq_zero_iff]
    have h1 : H2.mk (n • ζ) = 0 := by
      change (QuotientAddGroup.mk' (B2' G ℚ) (n • ζ)) = 0
      rw [map_nsmul (QuotientAddGroup.mk' (B2' G ℚ)) n ζ]
      exact hw
    rw [H2.mk_eq_zero_iff, mem_B2', mem_B2] at h1
    obtain ⟨u, hu⟩ := h1
    rw [mem_B2', mem_B2]
    refine ⟨⟨fun σ => (1 / (n : ℚ)) * (u : G → ℚ) σ,
        (u : Cochain1 G ℚ).isLocallyConstant.comp (fun q => (1 / (n : ℚ)) * q)⟩, ?_⟩
    refine LocallyConstant.ext fun p => ?_
    obtain ⟨σ, τ⟩ := p
    have hu' : d1Fun (u : G → ℚ) (σ, τ) = (n : ℚ) * (ζ : Cochain2 G ℚ) (σ, τ) := by
      have h := congrArg (fun v : Cochain2 G ℚ => v (σ, τ)) hu
      simp only [d1Hom_apply] at h
      rw [d1Fun_apply, h, AddSubgroup.coe_nsmul]
      show n • ((ζ : Cochain2 G ℚ) (σ, τ)) = (n : ℚ) * (ζ : Cochain2 G ℚ) (σ, τ)
      rw [nsmul_eq_mul]
    show d1Fun (fun σ => (1 / (n : ℚ)) * (u : G → ℚ) σ) (σ, τ) =
      (ζ : Cochain2 G ℚ) (σ, τ)
    rw [d1Fun_const_mul]
    simp only [hu']
    rw [← mul_assoc, one_div, inv_mul_cancel₀ hnQ, one_mul]
  exact hmain z hz

/-- The class of a `3`-cocycle vanishes in `H³` exactly when the cocycle is a coboundary. -/
theorem H3_mk_eq_zero_iff {M : Type*} [AddCommGroup M] [DistribMulAction G M]
    [IsDiscreteGModule G M] (z : Z3 G M) : H3.mk z = 0 ↔ z ∈ B3' G M := by
  have h : (QuotientAddGroup.mk' (B3' G M)) z = 0 ↔ z ∈ B3' G M := by
    rw [← AddMonoidHom.mem_ker, QuotientAddGroup.ker_mk' (B3' G M)]
  exact h

/-- `H³(G,ℚ)` has no torsion: a class killed by `n ≠ 0` vanishes. -/
theorem H3_rat_eq_zero_of_nsmul_eq_zero (n : ℕ) (hn : n ≠ 0) {z : H3 G ℚ}
    (hz : n • z = 0) : z = 0 := by
  have hnQ : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hmain : ∀ w : H3 G ℚ, n • w = 0 → w = 0 := by
    intro w
    refine QuotientAddGroup.induction_on w ?_
    intro ζ hw
    change H3.mk ζ = 0
    rw [H3_mk_eq_zero_iff]
    have h1 : H3.mk (n • ζ) = 0 := by
      change (QuotientAddGroup.mk' (B3' G ℚ) (n • ζ)) = 0
      rw [map_nsmul (QuotientAddGroup.mk' (B3' G ℚ)) n ζ]
      exact hw
    have hζ : (n • ζ) ∈ B3' G ℚ := (H3_mk_eq_zero_iff (n • ζ)).mp h1
    rw [mem_B3', B3, AddMonoidHom.mem_range] at hζ
    obtain ⟨u, hu⟩ := hζ
    rw [mem_B3', B3, AddMonoidHom.mem_range]
    refine ⟨⟨fun p : G × G => (1 / (n : ℚ)) * (u : G × G → ℚ) p,
        (u : Cochain2 G ℚ).isLocallyConstant.comp (fun q => (1 / (n : ℚ)) * q)⟩, ?_⟩
    refine LocallyConstant.ext fun p => ?_
    obtain ⟨σ, τ, ρ⟩ := p
    have hu' : d2Fun (u : G × G → ℚ) (σ, τ, ρ) =
        (n : ℚ) * (ζ : Cochain3 G ℚ) (σ, τ, ρ) := by
      have h := congrArg (fun v : Cochain3 G ℚ => v (σ, τ, ρ)) hu
      simp only [d2Hom_apply] at h
      rw [d2Fun_apply, h, AddSubgroup.coe_nsmul]
      show n • ((ζ : Cochain3 G ℚ) (σ, τ, ρ)) = (n : ℚ) * (ζ : Cochain3 G ℚ) (σ, τ, ρ)
      rw [nsmul_eq_mul]
    show d2Fun (fun p : G × G => (1 / (n : ℚ)) * (u : G × G → ℚ) p) (σ, τ, ρ) =
      (ζ : Cochain3 G ℚ) (σ, τ, ρ)
    rw [d2Fun_const_mul]
    simp only [hu']
    rw [← mul_assoc, one_div, inv_mul_cancel₀ hnQ, one_mul]
  exact hmain z hz

/-! ### The coefficient sequence `0 → ℤ → ℚ → ℚ/ℤ → 0` -/

/-- The coefficient sequence `0 → ℤ → ℚ → ℚ/ℤ → 0`, for the trivial `G`-actions on `ℤ` and
`ℚ/ℤ` (the action on `ℚ` being the canonical trivial one). -/
def ratSES [DistribMulAction G ℤ] [DistribMulAction G QZ]
    (htrivZ : ∀ (σ : G) (n : ℤ), σ • n = n)
    (htrivQZ : ∀ (σ : G) (r : QZ), σ • r = r) : CoeffSES G ℤ ℚ QZ where
  f := { toAddMonoidHom := Int.castAddHom ℚ
         map_smul' := fun σ n => by
           show ((σ • n : ℤ) : ℚ) = σ • ((n : ℤ) : ℚ)
           rw [htrivZ σ n]
           rfl }
  g := { toAddMonoidHom := QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ))
         map_smul' := fun σ x => by
           show QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ)) (σ • x) =
             σ • QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ)) x
           rw [show σ • x = x from rfl,
             htrivQZ σ (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ)) x)] }
  injective_f := fun a b h => Int.cast_injective h
  surjective_g := by
    intro c
    refine QuotientAddGroup.induction_on c ?_
    intro b
    exact ⟨b, QuotientAddGroup.mk'_apply _ b⟩
  exact := by
    intro b
    have hnorm : (AddSubgroup.zmultiples (1 : ℚ)).Normal := inferInstance
    have hkey : (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ))) b = 0 ↔
        b ∈ AddSubgroup.zmultiples (1 : ℚ) := by
      rw [QuotientAddGroup.mk'_apply]
      exact @QuotientAddGroup.eq_zero_iff ℚ _ (AddSubgroup.zmultiples (1 : ℚ)) hnorm b
    rw [hkey]
    constructor
    · intro hb
      obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp hb
      refine ⟨m, ?_⟩
      show ((m : ℤ) : ℚ) = b
      rw [← hm]
      simp
    · rintro ⟨a, rfl⟩
      show ((a : ℤ) : ℚ) ∈ AddSubgroup.zmultiples (1 : ℚ)
      exact AddSubgroup.mem_zmultiples_iff.mpr ⟨a, by simp⟩

end Aux

theorem twoTorsionH3_natCard_eq_quot_bockstein
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [DistribMulAction G ℤ] [Work.ConCohomology.IsDiscreteGModule G ℤ]
    [DistribMulAction G (ZMod 2)] [Work.ConCohomology.IsDiscreteGModule G (ZMod 2)]
    [DistribMulAction G Work.ShafarevichKoch.QZ]
    [Work.ConCohomology.IsDiscreteGModule G Work.ShafarevichKoch.QZ]
    (htrivZ : ∀ (σ : G) (n : ℤ), σ • n = n)
    (htriv2 : ∀ (σ : G) (m : ZMod 2), σ • m = m)
    (htrivQZ : ∀ (σ : G) (r : Work.ShafarevichKoch.QZ), σ • r = r)
    (hfin2 : Finite (Work.ConCohomology.H2 G ℤ))
    (hfin3 : Finite (Work.ShafarevichKoch.H3 G ℤ)) :
    Nat.card (Work.ShafarevichKoch.twoTorsionH3 G) =
      Nat.card (Work.ConCohomology.H2 G (ZMod 2) ⧸
        AddSubgroup.closure (Set.range (Work.ConCohomology.connecting1
          (Work.ShafarevichKoch.Bockstein.muTwoSES (G := G) htriv2 htrivQZ)))) := by
  classical
  haveI : Finite (H2 G ℤ) := hfin2
  haveI : Finite (H3 G ℤ) := hfin3
  -- ## The `μ₂`-sequence and the identification `H²(G,ℤ/2)/im δ¹ ≅ H²(G,ℚ/ℤ)[2]`
  let S₁ : CoeffSES G (ZMod 2) QZ QZ := muTwoSES (G := G) htriv2 htrivQZ
  have hg₂ : ∀ y : H2 G QZ, H2Map S₁.g y = (2 : ℕ) • y :=
    fun y => H2Map_eq_nsmul_of_apply_eq 2 S₁.g (fun m => muTwoDoubleEqHom_apply htrivQZ m) y
  have hclos : AddSubgroup.closure (Set.range (connecting1 S₁)) = (H2Map S₁.f).ker := by
    apply le_antisymm
    · rw [AddSubgroup.closure_le]
      rintro x ⟨y, rfl⟩
      exact H2Map_connecting1 S₁ y
    · intro x hx
      rw [AddMonoidHom.mem_ker] at hx
      obtain ⟨y, hy⟩ := (exact_H2_A S₁ x).mp hx
      exact AddSubgroup.subset_closure ⟨y, hy⟩
  have hkerf : (H2Map S₁.f).range = (H2Map S₁.g).ker := by
    apply AddSubgroup.ext
    intro x
    rw [AddMonoidHom.mem_range, AddMonoidHom.mem_ker]
    exact (exact_H2_B S₁ x).symm
  have hker2 : ∀ x : H2 G QZ, x ∈ (H2Map S₁.g).ker ↔ (2 : ℕ) • x = 0 :=
    fun x => by rw [AddMonoidHom.mem_ker, hg₂ x]
  have hcard1 : Nat.card (H2 G (ZMod 2) ⧸ AddSubgroup.closure (Set.range (connecting1 S₁))) =
      Nat.card {b : H2 G QZ // (2 : ℕ) • b = 0} := by
    rw [hclos]
    calc Nat.card (H2 G (ZMod 2) ⧸ (H2Map S₁.f).ker)
        = Nat.card (H2Map S₁.f).range :=
          Nat.card_congr (QuotientAddGroup.quotientKerEquivRange (H2Map S₁.f)).toEquiv
      _ = Nat.card (H2Map S₁.g).ker := by rw [hkerf]
      _ = Nat.card {b : H2 G QZ // (2 : ℕ) • b = 0} :=
          Nat.card_congr (Equiv.subtypeEquivRight hker2)
  -- ## The `ℚ`-sequence and the identification `H²(G,ℚ/ℤ)[2] ≅ H³(G,ℤ)[2]`
  let S₂ : CoeffSES G ℤ ℚ QZ := ratSES (G := G) htrivZ htrivQZ
  let δ₂ : H2 G QZ →+ H3 G ℤ := connecting2Map S₂
  have hspec₂ : ∀ (z : Z2 G QZ) (u : Cochain2 G ℚ),
      (∀ p : G × G, S₂.g (u p) = (z : Cochain2 G QZ) p) →
      ∃ w : Z3 G ℤ, H3.mk w = δ₂ (H2.mk z) ∧
        (∀ p : G × G × G, S₂.f ((w : G × G × G → ℤ) p) = d2Fun (u : G × G → ℚ) p) :=
    connecting2Map_spec S₂
  have hex2 : ∀ x : H2 G QZ, δ₂ x = 0 ↔ ∃ y : H2 G ℚ, H2Map S₂.g y = x :=
    exact_H2_C S₂ δ₂ hspec₂
  have hex3 : ∀ x : H3 G ℤ, H3Map S₂.f x = 0 ↔ ∃ y : H2 G QZ, δ₂ y = x :=
    exact_H3_A S₂ δ₂ hspec₂
  have hexβ : ∀ x : H2 G ℚ, H2Map S₂.g x = 0 ↔ ∃ y : H2 G ℤ, H2Map S₂.f y = x :=
    exact_H2_B S₂
  -- finiteness of `H²(G,ℤ)` forces the coefficient map `H²(G,ℤ) → H²(G,ℚ)` to vanish
  have hn2 : Nat.card (H2 G ℤ) ≠ 0 := by
    haveI : Nonempty (H2 G ℤ) := ⟨0⟩
    exact (Nat.card_pos (α := H2 G ℤ)).ne'
  have hkill : ∀ y : H2 G ℤ, H2Map S₂.f y = 0 := by
    intro y
    refine H2_rat_eq_zero_of_nsmul_eq_zero (Nat.card (H2 G ℤ)) hn2 ?_
    rw [← map_nsmul, card_nsmul_eq_zero', map_zero]
  -- the connecting map `δ₂` is injective on the `2`-torsion of `H²(G,ℚ/ℤ)`
  have hdisj : ∀ x : H2 G QZ, δ₂ x = 0 → (2 : ℕ) • x = 0 → x = 0 := by
    intro x hx hx2
    obtain ⟨w, hw⟩ := (hex2 x).mp hx
    have hgw : H2Map S₂.g ((2 : ℕ) • w) = 0 := by
      rw [map_nsmul, hw, hx2]
    obtain ⟨y, hy⟩ := (hexβ ((2 : ℕ) • w)).mp hgw
    have h2w : (2 : ℕ) • w = 0 := by rw [← hy, hkill y]
    have hw0 : w = 0 := H2_rat_eq_zero_of_nsmul_eq_zero 2 (by norm_num) h2w
    rw [← hw, hw0, map_zero]
  -- and it covers the whole `2`-torsion of `H³(G,ℤ)`
  let Φ : {b : H2 G QZ // (2 : ℕ) • b = 0} → {c : H3 G ℤ // (2 : ℕ) • c = 0} :=
    fun b => ⟨δ₂ b.1, by rw [← map_nsmul, b.2, map_zero]⟩
  have hΦinj : Function.Injective Φ := by
    intro b b' hbb
    have h1 : δ₂ b.1 = δ₂ b'.1 := congrArg Subtype.val hbb
    have hδ : δ₂ (b.1 - b'.1) = 0 := by rw [map_sub, h1, sub_self]
    have ht : (2 : ℕ) • (b.1 - b'.1) = 0 := by rw [nsmul_sub, b.2, b'.2, sub_zero]
    have hz : b.1 - b'.1 = 0 := hdisj _ hδ ht
    exact Subtype.ext (sub_eq_zero.mp hz)
  have hΦsurj : Function.Surjective Φ := by
    intro c
    have hγ : H3Map S₂.f c.1 = 0 := by
      refine H3_rat_eq_zero_of_nsmul_eq_zero 2 (by norm_num) ?_
      rw [← map_nsmul, c.2, map_zero]
    obtain ⟨b, hb⟩ := (hex3 c.1).mp hγ
    have hk : δ₂ ((2 : ℕ) • b) = 0 := by rw [map_nsmul, hb, c.2]
    obtain ⟨w, hw⟩ := (hex2 _).mp hk
    obtain ⟨w', hw'⟩ := exists_nsmul_eq_H2_rat 2 (by norm_num) w
    refine ⟨⟨b - H2Map S₂.g w', ?_⟩, ?_⟩
    · have h1 : (2 : ℕ) • (H2Map S₂.g w') = (2 : ℕ) • b := by
        rw [← map_nsmul, hw', hw]
      rw [nsmul_sub, h1, sub_self]
    · apply Subtype.ext
      change δ₂ (b - H2Map S₂.g w') = c.1
      rw [map_sub, hb]
      have hz : δ₂ (H2Map S₂.g w') = 0 := (hex2 _).mpr ⟨w', rfl⟩
      rw [hz, sub_zero]
  have hcard2 : Nat.card {b : H2 G QZ // (2 : ℕ) • b = 0} = Nat.card (twoTorsionH3 G) :=
    Nat.card_congr (Equiv.ofBijective Φ ⟨hΦinj, hΦsurj⟩)
  exact hcard2.symm.trans hcard1.symm

end Work.ShafarevichKoch.Bockstein
