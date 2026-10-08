import Mathlib
import Submission.Work.BG.lamOrbitOfU_lamEquiv
import Submission.Work.BG.lamOrbitOfU_disjoint_bset
import Submission.Work.BG.inner_coherence_coeff
import Submission.Work.BG.bset_orbit_struct

namespace Work.BG

/-! ## A local, self-contained form of "`Λ(a)` is disjoint from `𝒮(χ)`"

The module `Submission.Work.BG.lamOrbitOfU_disjoint_bset` states exactly the fact needed below,
but its proof goes through `Work.BG.constituent_trivial_of_sconj_mem`.  We reproduce that short
argument here (so that the result below does not have to wait on that file), following the route
described in the header of `lamOrbitOfU_disjoint_bset`. -/
open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
private theorem not_mem_bset_of_mem_lamOrbitOfU {G : Type} [Group G] [Finite G] [Fintype G]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) (hDC : Work.GW2.C16.Compat D C)
    (K : Subgroup G)
    (Knorm : ∀ u ∈ D.U, ∀ x ∈ K, u * x * u⁻¹ ∈ K)
    (h1 : ∀ x ∈ K, D.t1 * x * D.t1⁻¹ = x⁻¹)
    (h2 : ∀ x ∈ K, D.t2 * x * D.t2⁻¹ = x⁻¹)
    [Invertible (Nat.card ↥C.P.H0 : ℂ)] [Fintype ↥C.P.H0] [Fintype ↥(Work.GW2.C16.Uin C)]
    [Invertible (Nat.card ↥(Work.GW2.C16.Uin C) : ℂ)]
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (χ : ClassFunction G ℂ)
    (hsl : ∀ ν ∈ Work.GW2.C16.bset C f χ, Work.BG.sconj C ν ∈ Work.BG.lamOrbit C ν)
    (a : IrreducibleCharacter ↥(Work.GW2.C16.Uin C)) (ha : Work.BG.nontrivialOn C K a)
    {ν : ClassFunction ↥C.P.H0 ℂ}
    (hν : ν ∈ Work.BG.lamOrbitOfU C (a : ClassFunction ↥(Work.GW2.C16.Uin C) ℂ)) :
    ν ∉ Work.GW2.C16.bset C f χ := by
  classical
  intro hb
  -- `ν ∈ Irr(H₀)` with `a` a constituent of `ν|_U`; `ν ∈ 𝒮(χ)` gives `ν^s ∈ Λν`.
  have hνirr : IsIrreducibleCharacter ν := hν.1
  have hairr : IsIrreducibleCharacter (a : ClassFunction ↥(Work.GW2.C16.Uin C) ℂ) := a.2
  have hcon : ClassFunction.inner (ClassFunction.restrict (Work.GW2.C16.Uin C) ν)
      (a : ClassFunction ↥(Work.GW2.C16.Uin C) ℂ) ≠ 0 := hν.2
  have hm : Work.BG.sconj C ν ∈ Work.BG.lamOrbit C ν := hsl ν hb
  -- transport `Knorm` across `C.P.U = D.U`
  have hKnorm' : ∀ u ∈ C.P.U, ∀ x ∈ K, u * x * u⁻¹ ∈ K := by
    intro u hu x hx
    exact Knorm u (hDC.U_eq ▸ hu) x hx
  -- every `U`-constituent of `ν|_U` is trivial on `K`
  have htriv :=
    Work.BG.constituent_trivial_of_sconj_mem D C K hDC hKnorm' h1 h2 hνirr hm hairr hcon
  -- contradicting `nontrivialOn C K a`
  obtain ⟨u, huK, hune⟩ := ha
  have humem : u ∈ Work.BG.KuSub C K := by
    rw [Work.BG.KuSub, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact huK
  exact hune (htriv u humem)

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
/-- **Equal multiplicities on `Λ(a)`.**  For an irreducible `χ` of `G`, a coherent map `f`, the
standing hypothesis `hsl : ν^s ∈ Λν` on `𝒮(χ)`, and `a ∈ Irr(U)` nontrivial on `K`, all members
of `lamOrbitOfU C a` occur in `χ|_{H₀}` with the *same* multiplicity `⟨χ|_{H₀}, ν⟩`.

Route: `hν` gives `ν ∈ Irr(H₀)` and `⟨ν|_U, a⟩ ≠ 0` (and the same for `ν'`), so
`Work.BG.lamOrbitOfU_lamEquiv` gives `LamEquiv C ν ν'`.  Then `Work.BG.inner_coherence_coeff`
(coherence clause (iii) plus Frobenius reciprocity) gives
`⟨χ, f ν - f ν'⟩ = ⟨χ|_{H₀}, ν - ν'⟩`, while `Work.BG.lamOrbitOfU_disjoint_bset` gives
`ν ∉ 𝒮(χ)` and `ν' ∉ 𝒮(χ)`, hence `⟨χ, f ν⟩ = 0 = ⟨χ, f ν'⟩` (membership in `bset` requires
irreducibility, which holds).  So `⟨χ|_{H₀}, ν - ν'⟩ = 0`, and
`⟨χ|_{H₀}, ν - ν'⟩ = ⟨χ|_{H₀}, ν⟩ - ⟨χ|_{H₀}, ν'⟩` (`ClassFunction.inner_sub_right`) gives the
claim.  `Invertible (Nat.card G : ℂ)` is synthesised automatically from `[Fintype G]`, and `hχ`,
`hKU` are not needed by this route. -/
theorem lamOrbitOfU_mult_eq {G : Type} [Group G] [Finite G] [Fintype G]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) (hDC : Work.GW2.C16.Compat D C)
    (hS3 : Work.GW2.C16.Sec3Hyp D) (K : Subgroup G) (hKU : K ≤ D.U)
    (Knorm : ∀ u ∈ D.U, ∀ x ∈ K, u * x * u⁻¹ ∈ K)
    (h1 : ∀ x ∈ K, D.t1 * x * D.t1⁻¹ = x⁻¹)
    (h2 : ∀ x ∈ K, D.t2 * x * D.t2⁻¹ = x⁻¹)
    [Invertible (Nat.card ↥C.P.H0 : ℂ)] [Fintype ↥C.P.H0] [Fintype ↥(Work.GW2.C16.Uin C)]
    [Invertible (Nat.card ↥(Work.GW2.C16.Uin C) : ℂ)]
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ)
    (hf : Work.GW2.C16.IsCoherent C f)
    (χ : ClassFunction G ℂ) (hχ : IsIrreducibleCharacter χ)
    (hsl : ∀ ν ∈ Work.GW2.C16.bset C f χ, Work.BG.sconj C ν ∈ Work.BG.lamOrbit C ν)
    (a : IrreducibleCharacter ↥(Work.GW2.C16.Uin C)) (ha : Work.BG.nontrivialOn C K a)
    {ν ν' : ClassFunction ↥C.P.H0 ℂ}
    (hν : ν ∈ Work.BG.lamOrbitOfU C (a : ClassFunction ↥(Work.GW2.C16.Uin C) ℂ))
    (hν' : ν' ∈ Work.BG.lamOrbitOfU C (a : ClassFunction ↥(Work.GW2.C16.Uin C) ℂ)) :
    ClassFunction.inner (ClassFunction.restrict C.P.H0 χ) ν =
      ClassFunction.inner (ClassFunction.restrict C.P.H0 χ) ν' := by
  classical
  have hairr : IsIrreducibleCharacter (a : ClassFunction ↥(Work.GW2.C16.Uin C) ℂ) := a.2
  have hνirr : IsIrreducibleCharacter ν := hν.1
  have hν'irr : IsIrreducibleCharacter ν' := hν'.1
  -- `ν` and `ν'` are `Λ`-equivalent (both restrict to `U` with `a` as a constituent)
  have hlam : Work.BG.LamEquiv C ν ν' :=
    Work.BG.lamOrbitOfU_lamEquiv D C hDC hS3 hνirr hν'irr hairr hν.2 hν'.2
  -- coherence clause (iii) + Frobenius reciprocity
  have hcoh := Work.BG.inner_coherence_coeff C f hf χ hνirr hν'irr hlam
  -- neither `ν` nor `ν'` lies in `𝒮(χ)`, so `f ν` and `f ν'` are orthogonal to `χ`
  have hnb : ν ∉ Work.GW2.C16.bset C f χ :=
    not_mem_bset_of_mem_lamOrbitOfU D C hDC K Knorm h1 h2 f χ hsl a ha hν
  have hnb' : ν' ∉ Work.GW2.C16.bset C f χ :=
    not_mem_bset_of_mem_lamOrbitOfU D C hDC K Knorm h1 h2 f χ hsl a ha hν'
  have hz : ClassFunction.inner χ (f ν) = 0 := by
    by_contra h
    exact hnb ⟨hνirr, h⟩
  have hz' : ClassFunction.inner χ (f ν') = 0 := by
    by_contra h
    exact hnb' ⟨hν'irr, h⟩
  have h0 : ClassFunction.inner χ (f ν - f ν') = 0 := by
    rw [ClassFunction.inner_sub_right, hz, hz', sub_zero]
  rw [hcoh, ClassFunction.inner_sub_right] at h0
  exact sub_eq_zero.mp h0

end Work.BG
