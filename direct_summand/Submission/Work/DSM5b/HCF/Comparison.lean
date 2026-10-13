import Submission.Work.DSM5b.HCF.Complex
import Submission.Work.DSM5b.HCF.sizeExact
import Submission.Work.DSM5b.HCF.filtrationSES
import Submission.Work.DSM5b.HCF.filtrationLadder
import Submission.Work.DSM5b.HCF.level_quasiIso
import Submission.Work.DSM5b.HCF.quasiIso_toStc_of_bijective
import Submission.Work.DSM5b.HCF.quasiIso_middle_of_shortExact

/-!
# The honest tuple complex is quasi-isomorphic to the sorted complex

The comparison map `toStc : Htc 𝒜 ⟶ Stc 𝒜` (restriction of a cochain on all tuples to the
increasing ones) is a quasi-isomorphism, for every coefficient system `𝒜` on a finite linearly
ordered index type `ι`.

The proof is the descending induction on the size filtration of `𝒜`:

* the `k`-th stage is the sub-system `𝒜_{≥k} = subCF 𝒜 k` of coefficients supported on subsets of
  size at least `k`, and the consecutive quotients `𝒜_{=k} = exactlyCoeff 𝒜 k` are the systems
  supported on the subsets of size exactly `k`;
* each stage fits into a short exact sequence of complexes, for both the honest and the sorted
  complex (`Work.DSM5b.HCF.filtrationSES`), and the comparison map is a morphism of these two short
  exact sequences (`Work.DSM5b.HCF.filtrationLadder`): the five-term exactness for the middle term
  (`Work.DSM5b.HCF.quasiIso_middle_of_shortExact`) therefore reduces the comparison for the stage
  `k` to the comparison for the stage `k+1` together with the comparison for the graded piece
  `𝒜_{=k}`, which is `Work.DSM5b.HCF.level_quasiIso` (proved from the surjection-complex
  computation `Work.DSM5b.HCF.surj_cohomology`);
* the induction starts above the number of elements of `ι`, where every coefficient module vanishes
  (so both complexes are trivial), and it ends at the stage `0`, which is the whole system up to
  componentwise bijection; the transfer along a bijective morphism of coefficient systems is
  `Work.DSM5b.HCF.quasiIso_toStc_of_bijective`.
-/

namespace Work.DSM5b.HCF

open CategoryTheory Work.DSM5b

universe u

variable {R : Type u} [CommRing R] {ι : Type u} [Fintype ι] [DecidableEq ι] [LinearOrder ι]

/-- A submodule equal to `⊥` has a subsingleton underlying type. -/
private lemma subsingleton_of_eq_bot {M : Type*} [AddCommGroup M] [Module R M]
    {p : Submodule R M} (h : p = ⊥) : Subsingleton (↥p) := by
  subst h
  exact ⟨fun a b => Subtype.ext (by
    rw [(Submodule.mem_bot R).mp a.2, (Submodule.mem_bot R).mp b.2])⟩

/-- A quotient of a subsingleton module is a subsingleton. -/
private lemma subsingleton_quot {M : Type*} [AddCommGroup M] [Module R M] (q : Submodule R M)
    (h : Subsingleton M) : Subsingleton (M ⧸ q) := by
  constructor
  intro x y
  obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective q x
  obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective q y
  rw [Subsingleton.elim a b]

variable (𝒜 : CoeffSys R ι)

lemma sizeSubSys_zero_top (S : Finset ι) : (CoeffSys.sizeSubSys 𝒜 0).N S = ⊤ := by
  show (if 0 ≤ S.card then (⊤ : Submodule R (𝒜.M S)) else ⊥) = ⊤
  exact ite_eq_left (Nat.zero_le _)

/-- The stage `0` of the size filtration, as a morphism of coefficient systems into `𝒜` (it is the
inclusion of the full coefficients, i.e. componentwise bijective). -/
noncomputable def subCFZeroHom : CoeffSys.Hom (CoeffSys.subCF 𝒜 0) 𝒜 where
  φ S := Submodule.subtype ((CoeffSys.sizeSubSys 𝒜 0).N S)
  comm := by
    intro S T h x
    rfl

lemma subCFZeroHom_bijective : ∀ S : Finset ι, Function.Bijective ((subCFZeroHom 𝒜).φ S) := by
  intro S
  have htop := sizeSubSys_zero_top 𝒜 S
  exact ⟨fun a b hab => Subtype.ext hab, fun b => ⟨⟨b, htop ▸ Submodule.mem_top⟩, rfl⟩⟩

/-- Every stage of the size filtration above the number of elements of `ι` is the zero system, and
the zero morphism to the graded piece `𝒜_{= ♯ι}` is componentwise bijective (both sides vanish). -/
noncomputable def subCFTopHom (j : ℕ) :
    CoeffSys.Hom (CoeffSys.subCF 𝒜 j) (CoeffSys.exactlyCoeff 𝒜 (Fintype.card ι + 1)) where
  φ _ := 0
  comm := by
    intro S T h x
    simp

lemma subCFTopHom_bijective {j : ℕ} (hj : Fintype.card ι + 1 ≤ j) :
    ∀ S : Finset ι, Function.Bijective ((subCFTopHom 𝒜 j).φ S) := by
  intro S
  have hbot : (CoeffSys.sizeSubSys 𝒜 j).N S = ⊥ := by
    show (if j ≤ S.card then (⊤ : Submodule R (𝒜.M S)) else ⊥) = ⊥
    exact ite_eq_right (by have := Finset.card_le_univ S; omega)
  have hbot' : (CoeffSys.sizeSubSys 𝒜 (Fintype.card ι + 1)).N S = ⊥ := by
    show (if Fintype.card ι + 1 ≤ S.card then (⊤ : Submodule R (𝒜.M S)) else ⊥) = ⊥
    exact ite_eq_right (by have := Finset.card_le_univ S; omega)
  haveI h1 : Subsingleton ((CoeffSys.subCF 𝒜 j).M S) := by
    change Subsingleton (↥((CoeffSys.sizeSubSys 𝒜 j).N S))
    rw [hbot]
    exact subsingleton_of_eq_bot (p := ⊥) rfl
  haveI h2 : Subsingleton ((CoeffSys.exactlyCoeff 𝒜 (Fintype.card ι + 1)).M S) := by
    change Subsingleton (↥((CoeffSys.sizeSubSys 𝒜 (Fintype.card ι + 1)).N S) ⧸
      (Submodule.inclusion (CoeffSys.sizeSubSys_mono 𝒜 (Fintype.card ι + 1) S)).range)
    exact subsingleton_quot _ (subsingleton_of_eq_bot hbot')
  exact ⟨fun a b _ => Subsingleton.elim a b, fun b => ⟨0, Subsingleton.elim _ b⟩⟩

/-- The inverse of `subCFZeroHom`: the componentwise inverse of the (bijective) inclusion of the
full coefficients. -/
noncomputable def subCFZeroHomInv : CoeffSys.Hom 𝒜 (CoeffSys.subCF 𝒜 0) where
  φ S :=
    { toFun := fun x => ⟨x, (sizeSubSys_zero_top 𝒜 S).symm ▸ Submodule.mem_top⟩
      map_add' := fun a b => Subtype.ext rfl
      map_smul' := fun r a => Subtype.ext rfl }
  comm := by
    intro S T h x
    exact Subtype.ext rfl

lemma subCFZeroHomInv_bijective :
    ∀ S : Finset ι, Function.Bijective ((subCFZeroHomInv 𝒜).φ S) := by
  intro S
  refine ⟨fun a b hab => congrArg Subtype.val hab, fun b => ⟨b.1, Subtype.ext rfl⟩⟩

/-- **The honest tuple complex is quasi-isomorphic to the sorted complex**, for every coefficient
system on a finite linearly ordered index type. -/
theorem toStc_quasiIso : QuasiIso (toStcHom 𝒜) := by
  have hbase : ∀ j, Fintype.card ι + 1 ≤ j →
      QuasiIso (toStcHom (CoeffSys.subCF 𝒜 j)) := by
    intro j hj
    exact quasiIso_toStc_of_bijective (subCFTopHom 𝒜 j) (subCFTopHom_bijective 𝒜 hj)
      (level_quasiIso 𝒜 (Fintype.card ι + 1))
  have hstep : ∀ j, j < Fintype.card ι + 1 →
      QuasiIso (toStcHom (CoeffSys.subCF 𝒜 (j + 1))) →
      QuasiIso (toStcHom (CoeffSys.subCF 𝒜 j)) := by
    intro j _ hnext
    obtain ⟨φ, h1, h2, h3⟩ := filtrationLadder 𝒜 j
    obtain ⟨hS1, hS2⟩ := filtrationSES 𝒜 j
    have ht := quasiIso_middle_of_shortExact φ hS1 hS2
      (by rw [h1]; exact hnext) (by rw [h3]; exact level_quasiIso 𝒜 j)
    rwa [h2] at ht
  have hdesc : ∀ d, ∀ j, j + d = Fintype.card ι + 1 →
      QuasiIso (toStcHom (CoeffSys.subCF 𝒜 j)) := by
    intro d
    induction d with
    | zero =>
      intro j hj
      rw [Nat.add_zero] at hj
      rw [hj]
      exact hbase _ le_rfl
    | succ d ih =>
      intro j hj
      exact hstep j (by omega) (ih (j + 1) (by omega))
  exact quasiIso_toStc_of_bijective (subCFZeroHomInv 𝒜) (subCFZeroHomInv_bijective 𝒜)
    (hdesc (Fintype.card ι + 1) 0 (by omega))

end Work.DSM5b.HCF
