import Mathlib
import Submission.Work.SSGRoute.PTembedding.kummer_ses_decomp
import Submission.Work.SSGRoute.PTembedding.h0_addUnits_addEquiv_decompField
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Local Kummer theory over a decomposition group

`H¹(D_A, μ_p) ≅ Fˣ ⧸ (Fˣ)^p` for the decomposition field `F = Ω^{D_A}` of a finite place `A`,
obtained from the low-degree exact sequence of the Kummer sequence
`1 → μ_p → Ωˣ → Ωˣ → 1` (`Work.SSGRoute.PTembedding.MupCard.exists_kummerSES_decomp`) together
with Hilbert 90 for `D_A` (`MupCard.hilbert90_decompH1`) and the identification
`H⁰(D_A, Ωˣ) = Fˣ` (`Work.SSGRoute.PTembedding.h0_addUnits_addEquiv_decompField`).
-/

open SSGRoute
open Work.SSGRoute

namespace Work.SSGRoute.PTembedding.MupCard

noncomputable section
set_option linter.style.haveILetI false

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω]

/-- **Local Kummer theory at a decomposition group.**  For a finite place `A` of `Ω` over the
number field `k`, the continuous `H¹` of the decomposition group `D_A = decomp k A` with
coefficients in `μ_p` is the `p`-Kummer group `Fˣ ⧸ (Fˣ)^p` of the decomposition field
`F = Ω^{D_A}`. -/
theorem card_H1_decomp_muAdd_eq_KummerGroup
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    Nat.card (Work.AbsoluteKummer.H1 ↥(SSGRoute.decomp k A) (MuAdd p K))
      = Nat.card (Work.SSGRoute.mup.KummerGroup p (Work.SSGRoute.mup.decompField k Ω A)) := by
  classical
  obtain ⟨S, -, hSπ⟩ := exists_kummerSES_decomp (p := p) (K := K) (ζ := ζ) (hζ := hζ)
    (hζK := hζK) (A := A) (hA := hA)
  obtain ⟨δ, hker, hrange⟩ := Work.AbsoluteKummer.SES.exists_connecting_exact S
  -- the projection of the Kummer sequence is the `p`-th power map
  have hpi : S.pi = powPi (p := p) (Ω := Ω) := AddMonoidHom.ext hSπ
  have hmapH0 : Work.GroupCohomology.mapH0 ↥(SSGRoute.decomp k A) S.pi S.pi_equivariant
      = Work.GroupCohomology.mapH0 ↥(SSGRoute.decomp k A) (powPi (p := p) (Ω := Ω))
          (powPi_equivariant (p := p) (Ω := Ω) (SSGRoute.decomp k A)) := by
    refine AddMonoidHom.ext (fun x => Subtype.ext ?_)
    exact hSπ ↑x
  -- the kernel of the connecting map is the image of the `p`-th power map on the invariants
  set A0 : AddSubgroup
      (↥(Work.AbsoluteKummer.H0 ↥(SSGRoute.decomp k A) (Additive (Units Ω)))) :=
    (Work.GroupCohomology.mapH0 ↥(SSGRoute.decomp k A) (powPi (p := p) (Ω := Ω))
      (powPi_equivariant (p := p) (Ω := Ω) (SSGRoute.decomp k A))).range with hA0
  have hkerA : δ.ker = A0 := by rw [← hker, hmapH0, hA0]
  -- Hilbert 90: `H¹(D_A, Ωˣ) = 0`, so the connecting map is onto
  have htop : δ.range = ⊤ := by
    rw [hrange, eq_top_iff]
    intro y _
    rw [AddMonoidHom.mem_ker]
    exact hilbert90_decompH1 k Ω A hA
      (Work.AbsoluteKummer.mapH1 S.iota S.iota_equivariant y)
  have hsurj : Function.Surjective δ := AddMonoidHom.range_eq_top.mp htop
  -- `H⁰(D_A, Ωˣ) = Fˣ`
  obtain ⟨e⟩ := Work.SSGRoute.PTembedding.h0_addUnits_addEquiv_decompField k Ω A hA
  -- under this identification, `H⁰(powPi)` is the `p`-th power map on `Fˣ`
  have he : ∀ x : ↥(Work.AbsoluteKummer.H0 ↥(SSGRoute.decomp k A) (Additive (Units Ω))),
      e ((Work.GroupCohomology.mapH0 ↥(SSGRoute.decomp k A) (powPi (p := p) (Ω := Ω))
          (powPi_equivariant (p := p) (Ω := Ω) (SSGRoute.decomp k A))) x)
        = Additive.ofMul (Additive.toMul (e x) ^ p) := by
    intro x
    have hx : (Work.GroupCohomology.mapH0 ↥(SSGRoute.decomp k A) (powPi (p := p) (Ω := Ω))
        (powPi_equivariant (p := p) (Ω := Ω) (SSGRoute.decomp k A))) x = p • x := by
      apply Subtype.ext
      show powPi (p := p) (x : Additive (Units Ω)) = p • (x : Additive (Units Ω))
      exact powPi_eq_nsmul _
    rw [hx, show e (p • x) = p • e x from map_nsmul (e.toAddMonoidHom) p x,
      ← powPi_eq_nsmul, powPi_apply]
  have he' : ∀ x : ↥(Work.AbsoluteKummer.H0 ↥(SSGRoute.decomp k A) (Additive (Units Ω))),
      e.toAddMonoidHom ((Work.GroupCohomology.mapH0 ↥(SSGRoute.decomp k A) (powPi (p := p) (Ω := Ω))
          (powPi_equivariant (p := p) (Ω := Ω) (SSGRoute.decomp k A))) x)
        = Additive.ofMul (Additive.toMul (e x) ^ p) := fun x => he x
  set S0 : Subgroup (↥(Work.SSGRoute.mup.decompField k Ω A))ˣ :=
    MonoidHom.range (powMonoidHom p) with hS0
  -- `e` carries the image of the `p`-th power map to `(Fˣ)^p`
  have hmap : AddSubgroup.map e.toAddMonoidHom A0 = S0.toAddSubgroup := by
    ext y
    rw [AddSubgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [AddMonoidHom.mem_range] at hx
      obtain ⟨w, rfl⟩ := hx
      rw [he' w, Additive.mem_toAddSubgroup, MonoidHom.mem_range]
      exact ⟨Additive.toMul (e w), rfl⟩
    · intro hy
      rw [Additive.mem_toAddSubgroup, MonoidHom.mem_range] at hy
      obtain ⟨w, hw⟩ := hy
      refine ⟨(Work.GroupCohomology.mapH0 ↥(SSGRoute.decomp k A) (powPi (p := p) (Ω := Ω))
          (powPi_equivariant (p := p) (Ω := Ω) (SSGRoute.decomp k A)))
          (e.symm (Additive.ofMul w)), AddMonoidHom.mem_range.mpr ⟨_, rfl⟩, ?_⟩
      rw [he' (e.symm (Additive.ofMul w)), AddEquiv.apply_symm_apply, toMul_ofMul,
        show w ^ p = Additive.toMul y from hw, ofMul_toMul]
  -- the two quotient identifications
  have hrel : ∀ a b : ↥(Work.AbsoluteKummer.H0 ↥(SSGRoute.decomp k A) (Additive (Units Ω))),
      QuotientAddGroup.leftRel δ.ker a b
        ↔ QuotientAddGroup.leftRel S0.toAddSubgroup (e a) (e b) := by
    intro a b
    rw [QuotientAddGroup.leftRel_apply, QuotientAddGroup.leftRel_apply, hkerA, ← hmap,
      AddSubgroup.mem_map]
    constructor
    · intro h
      exact ⟨-a + b, h, by simp⟩
    · rintro ⟨x, hx, hxeq⟩
      have h2 : e x = e (-a + b) := by
        rw [show e x = -e a + e b from hxeq]
        simp
      rwa [e.injective h2] at hx
  have hrel2 : ∀ a b : Additive (↥(Work.SSGRoute.mup.decompField k Ω A))ˣ,
      QuotientAddGroup.leftRel S0.toAddSubgroup a b
        ↔ QuotientGroup.leftRel S0 (Additive.toMul a) (Additive.toMul b) := by
    intro a b
    rw [QuotientAddGroup.leftRel_apply, QuotientGroup.leftRel_apply]
    simp
  calc Nat.card (Work.AbsoluteKummer.H1 ↥(SSGRoute.decomp k A) (MuAdd p K))
      = Nat.card ((↥(Work.AbsoluteKummer.H0 ↥(SSGRoute.decomp k A) (Additive (Units Ω))))
          ⧸ δ.ker) :=
        (Nat.card_congr
          (QuotientAddGroup.quotientKerEquivOfSurjective δ hsurj).toEquiv).symm
    _ = Nat.card ((Additive (↥(Work.SSGRoute.mup.decompField k Ω A))ˣ) ⧸ S0.toAddSubgroup) :=
        Nat.card_congr (Quotient.congr e.toEquiv hrel)
    _ = Nat.card (Work.SSGRoute.mup.KummerGroup p (Work.SSGRoute.mup.decompField k Ω A)) :=
        Nat.card_congr (Quotient.congr Additive.toMul hrel2)

end

end Work.SSGRoute.PTembedding.MupCard
