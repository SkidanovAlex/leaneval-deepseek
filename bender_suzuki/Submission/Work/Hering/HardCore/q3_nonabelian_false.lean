import Mathlib
import Submission.Work.Hering.HardCore.Defs
import Submission.Work.Higman.Class
import Submission.Work.Hering.AppVIII.appVIIIProp1
import Submission.Work.Hering.HardCore.q2_aut_solvable
import Submission.Work.Hering.Step5.mulAut_eight_order21
import Submission.Work.Hering.GL32.gl32_not_solvable
import Submission.Work.Hering.GL32.gl32_not_solvable_v2

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hering.HardCore

/-- `Aut(U)` is not solvable for a finite group `U` of order `8` and exponent two: `U ≅ (ℤ/2)³`
and `Aut((ℤ/2)³) ≅ GL(3,2)` is non-solvable. -/
theorem mulAut_eight_not_solvable {U : Type} [Group U] [Finite U]
    (hcard : Nat.card U = 8) (hexp : ∀ x : U, x * x = 1) :
    ¬ Group.IsSolvable (MulAut U) := by
  obtain ⟨e⟩ := Work.Hering.Step5.iso_fin3 hcard hexp
  intro hsol
  haveI := hsol
  exact Work.Hering.GL32.gl32_not_solvable_v2
    (Group.isSolvable_of_surjective (f := (MulAut.congr e).toMonoidHom)
      (MulAut.congr e).surjective)

/-- The contradiction of Peterfalvi I §4: a non-abelian Suzuki subgroup `D` of order `64` with
`V ≤ D ≤ C = C_G(V)`, normal in `G`, is impossible: `Z(D) = Ω₁(D) = V` has order `8`, so
`|D| = |Z(D)|²` and `hHig.1`'s classification clause gives `D ≅ A(3,φ)` with `φ ≠ 1` of odd
order; `q2_aut_solvable hHig.1 appVIIIProp1 hSuzD` (with the *proved*
`Work.Hering.AppVIII.appVIIIProp1`) then makes `MulAut ↥D` solvable, while `G`'s conjugation
maps onto `Aut(V) ≅ GL(3,2)` (`gl32_not_solvable`), a non-solvable quotient of a subgroup of
`MulAut ↥D`. -/
theorem q3_nonabelian_false {G : Type} [Group G] [Finite G]
    (hHig : Work.Higman.HigmanClassProp)
    (V C D : Subgroup G) (hV : V.Normal) (hcardV : Nat.card V = 8)
    (hexpV : ∀ x ∈ V, x * x = 1) (hC : C = Subgroup.centralizer ((V : Set G)))
    (hC2 : IsPGroup 2 ↥C) (hinv : ∀ x ∈ C, orderOf x = 2 → x ∈ V)
    (hAut : Work.Hering.ActsAsAut V hV)
    (hnotab : ¬ ∀ x ∈ C, ∀ y ∈ C, x * y = y * x)
    (hVD : V ≤ D) (hDC : D ≤ C) (hDn : D.Normal) (hcardD : Nat.card D = 64)
    (hnonab : ¬ ∀ x ∈ D, ∀ y ∈ D, x * y = y * x)
    (hSuzD : Work.Hering.IsSuzukiTwoGroup ↥D) :
    False := by
  -- `hHig.1` gives `Z(D) = Ω₁(D)` (the elements of `D` of order dividing two).
  obtain ⟨hcentD, -, -, -, -⟩ := hHig.1 ↥D hSuzD
  -- ### Step 1: `Z(D) = V`, hence `|Z(D)| = 8`.
  have hZV : ∀ z : ↥D, z ∈ Subgroup.center ↥D ↔ ((z : G) ∈ V) := by
    intro z
    rw [hcentD]
    constructor
    · intro hz
      have hz2 : (z : G) ^ 2 = 1 := by
        have h := congrArg (fun t : ↥D => (t : G)) hz
        simpa using h
      rcases eq_or_ne (z : G) 1 with h1 | h1
      · rw [h1]; exact V.one_mem
      · exact hinv (z : G) (hDC z.2) (orderOf_eq_prime hz2 h1)
    · intro hz
      have hz2 : (z : G) * (z : G) = 1 := hexpV (z : G) hz
      exact Subtype.ext (by simpa [pow_two] using hz2)
  have hZcard : Nat.card ↥(Subgroup.center ↥D) = 8 := by
    have hbij : Nat.card ↥(Subgroup.center ↥D) = Nat.card ↥V :=
      Nat.card_congr
        { toFun := fun z => ⟨((z : ↥D) : G), (hZV (z : ↥D)).mp z.2⟩
          invFun := fun v => ⟨⟨(v : G), hVD v.2⟩, (hZV ⟨(v : G), hVD v.2⟩).mpr v.2⟩
          left_inv := by rintro ⟨z, hz⟩; rfl
          right_inv := by rintro ⟨v, hv⟩; rfl }
    rw [hbij, hcardV]
  -- ### Step 2: `|D| = |Z(D)|²`, so Higman's classification makes `MulAut ↥D` solvable.
  have hcardD' : Nat.card ↥D = 64 := hcardD
  have hcard_sq : Nat.card ↥D = Nat.card ↥(Subgroup.center ↥D) ^ 2 := by
    rw [hZcard, hcardD']; norm_num
  have hsolD : Group.IsSolvable (MulAut ↥D) :=
    q2_aut_solvable hHig.1 Work.Hering.AppVIII.appVIIIProp1 hSuzD hcard_sq
  -- ### Step 3: `Aut(V) ≅ GL(3,2)` is not solvable, but it is a quotient of a subgroup of
  -- `MulAut ↥D`, contradiction.
  have hVns : ¬ Group.IsSolvable (MulAut ↥V) :=
    mulAut_eight_not_solvable hcardV (fun x => Subtype.ext (by simpa using hexpV x x.2))
  -- Conjugation on `V` is onto, by `hAut`.
  have hsurjV : Function.Surjective (MulAut.conjNormal (H := V) : G →* MulAut ↥V) := by
    intro φ
    obtain ⟨g, hg⟩ := hAut φ
    refine ⟨g, MulEquiv.ext (fun v => ?_)⟩
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    exact (congrArg Subtype.val (hg v)).symm
  -- A conjugation that is trivial on `D` is trivial on `V ≤ D`.
  have hker_le : (MulAut.conjNormal (H := D) : G →* MulAut ↥D).ker ≤
      (MulAut.conjNormal (H := V) : G →* MulAut ↥V).ker := by
    intro g hg
    rw [MonoidHom.mem_ker] at hg ⊢
    apply MulEquiv.ext
    intro v
    show (MulAut.conjNormal (H := V) g) v = v
    apply Subtype.ext
    have h1 : (MulAut.conjNormal (H := D) g) ⟨(v : G), hVD v.2⟩ = ⟨(v : G), hVD v.2⟩ := by
      rw [hg]; rfl
    have h2 := congrArg (fun w : ↥D => (w : G)) h1
    rw [MulAut.conjNormal_apply] at h2
    rw [MulAut.conjNormal_apply]
    exact h2
  -- `Aut(V)` is a quotient of `G/ker(conj on D)`, which is `≅ range(conj on D) ≤ MulAut ↥D`.
  have hψ : Function.Surjective
      (QuotientGroup.lift (MulAut.conjNormal (H := D) : G →* MulAut ↥D).ker
        (MulAut.conjNormal (H := V) : G →* MulAut ↥V) hker_le) := by
    intro φ
    obtain ⟨g, hg⟩ := hsurjV φ
    exact ⟨QuotientGroup.mk g, by rw [QuotientGroup.lift_mk]; exact hg⟩
  haveI : Group.IsSolvable (G ⧸ (MulAut.conjNormal (H := D) : G →* MulAut ↥D).ker) :=
    Group.isSolvable_of_surjective
      (f := (QuotientGroup.quotientKerEquivRange
        (MulAut.conjNormal (H := D) : G →* MulAut ↥D)).symm.toMonoidHom)
      (QuotientGroup.quotientKerEquivRange
        (MulAut.conjNormal (H := D) : G →* MulAut ↥D)).symm.surjective
  exact hVns (Group.isSolvable_of_surjective hψ)

end Work.Hering.HardCore
