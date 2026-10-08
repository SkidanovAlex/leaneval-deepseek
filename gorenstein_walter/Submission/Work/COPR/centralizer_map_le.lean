import Mathlib
import Submission.Work.COPR.Prelude13

namespace Work.COPR

/-- Bender 1981, 1.3, the `⊆` half of the centralizer identity: if `P` is a `p`-subgroup and `Y`
a normal `p'`-subgroup of a finite group `X`, then every element of `X/Y` centralizing the image of
`P` lies in the image of `C_X(P)`.

This is the "fixed points of a coprime action lift from a quotient" fact (Isaacs Cor. 3.28 /
BG Prop. 1.5(d)) with coprimality only against the normal subgroup `Y`. The workspace already has
`OddOrder.Isaacs.Ch04.coprime_fixedPoints_quotient_of_coprime_normal` (module
`Submission.OddOrder.Isaacs.Ch04_Commutators.ForwardFromCh03`, re-exported together with the
conjugation-action bridges `Work.COPR.coprime_card_of_isPGroup` / `Work.COPR.isSolvable_of_isPGroup`
by the prelude `Submission.Work.COPR.Prelude13`), which gives the elementwise lifting for an
abstract action `φ : A →* MulAut X` coprime on the normal `N`. -/
theorem centralizer_map_le {X : Type*} [Group X] [Finite X] (p : ℕ) [Fact p.Prime]
    (P Y : Subgroup X) [Y.Normal] (hP : IsPGroup p P) (hcop : Nat.Coprime p (Nat.card Y)) :
    Subgroup.centralizer ((P.map (QuotientGroup.mk' Y) : Subgroup (X ⧸ Y)) : Set (X ⧸ Y)) ≤
      (Subgroup.centralizer (P : Set X)).map (QuotientGroup.mk' Y) := by
  intro z hz
  -- Replace the element of the quotient by a representative.
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Y z
  -- The conjugation action of `P` on `X`.
  let φ : ↥P →* MulAut X := MulAut.conj.comp P.subtype
  have hφ : ∀ a : ↥P, φ a = MulAut.conj (a : X) := fun _ => rfl
  -- Being centralized in the quotient means the coset `xY` is invariant.
  have hg_fix : ∀ a : ↥P, ∃ n ∈ Y, (φ a) x = x * n := by
    intro a
    have hmem : QuotientGroup.mk' Y (a : X) ∈
        (P.map (QuotientGroup.mk' Y) : Subgroup (X ⧸ Y)) :=
      Subgroup.mem_map_of_mem _ a.property
    have hcomm : QuotientGroup.mk' Y (a : X) * QuotientGroup.mk' Y x =
        QuotientGroup.mk' Y x * QuotientGroup.mk' Y (a : X) :=
      (Subgroup.mem_centralizer_iff.mp hz) _ hmem
    have h1 : QuotientGroup.mk' Y x =
        QuotientGroup.mk' Y ((a : X) * x * (a : X)⁻¹) := by
      rw [map_mul, map_mul, map_inv, hcomm, mul_assoc, mul_inv_cancel, mul_one]
    obtain ⟨n, hn, hnx⟩ := (QuotientGroup.mk'_eq_mk' Y).mp h1
    exact ⟨n, hn, by rw [hφ, MulAut.conj_apply]; exact hnx.symm⟩
  -- The hypotheses of the coprime lifting lemma.
  have hCop : Nat.Coprime (Nat.card ↥P) (Nat.card ↥Y) :=
    coprime_card_of_isPGroup p hP hcop
  have hSolv : Group.IsSolvable ↥P ∨ Group.IsSolvable ↥Y :=
    Or.inl (isSolvable_of_isPGroup p hP)
  have hN_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ Y := by
    rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
    intro a g hg
    rw [hφ, MulAut.conj_apply]
    exact Subgroup.Normal.conj_mem inferInstance g hg (a : X)
  obtain ⟨c, hc_fix, n, hn, hcn⟩ :=
    OddOrder.Isaacs.Ch04.coprime_fixedPoints_quotient_of_coprime_normal
      (φ := φ) (N := Y) hCop hSolv hN_inv hg_fix
  refine Subgroup.mem_map.mpr ⟨c, ?_, ?_⟩
  · -- `c` centralizes `P` because it is fixed by the conjugation action.
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h := hc_fix ⟨y, hy⟩
    rw [hφ, MulAut.conj_apply] at h
    exact mul_inv_eq_iff_eq_mul.mp h
  · -- `c` and `x` have the same image in the quotient.
    exact (QuotientGroup.mk'_eq_mk' Y).mpr
      ⟨n⁻¹, Y.inv_mem hn, by rw [hcn, mul_assoc, mul_inv_cancel, mul_one]⟩

end Work.COPR
