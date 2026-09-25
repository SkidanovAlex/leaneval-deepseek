import Mathlib
import Submission.Work.CFT.ClassFormation.Defs
import Submission.Work.CFT.ClassFormation.Schur.finite_HnZ

/-!
# Finiteness of `H_n(G, ℤ)`

The integral homology `H_n(G, ℤ)` of a finite group `G` is annihilated by `|G|`.  Together with
finite generation (proved in `Work.CFT.ClassFormation.Schur.finite_HnZ`) this forces it to be
finite; this file supplies the second half of that implication in the form needed by the
Shafarevich/class-formation development: a finitely generated abelian group whose elements are all
killed by a positive integer is finite.

The argument is elementary.  A finitely generated abelian group `M` is a quotient of some `ℤ^r`.
If `m • x = 0` for every `x : M` and some positive `m`, then the surjection `ℤ^r ↠ M` kills the
sublattice `m ℤ^r = range (LinearMap.lsmul ℤ _ m)`, hence factors through the finite quotient
`ModN ℤ^r m = ℤ^r ⧸ m ℤ^r`; a quotient of a finite group is finite.
-/

namespace Work.Tower.Shafarevich.CFT

theorem HnZ_finite (G : Type) [Group G] [Fintype G] (k : ℕ) (hk : 1 ≤ k)
    (hT : ∀ y : (Work.CFT.ClassFormation.HnZ G k : Type), (Fintype.card G : ℤ) • y = 0) :
    Finite (Work.CFT.ClassFormation.HnZ G k : Type) := by
  have _hk := hk
  classical
  -- `|G|` is positive, hence a valid modulus for `ZMod`/`ModN`.
  have hne : NeZero (Fintype.card G) := ⟨(Fintype.card_pos (α := G)).ne'⟩
  -- `H_k(G, ℤ)` is finitely generated over `ℤ`.
  have hfin : Module.Finite ℤ (Work.CFT.ClassFormation.HnZ G k : Type) :=
    Work.CFT.ClassFormation.Schur.finite_HnZ' G k
  -- A finite free presentation: a surjective `ℤ`-linear map `ℤ^r ↠ H_k(G, ℤ)`.
  obtain ⟨r, f, hf⟩ := Module.Finite.exists_fin' (R := ℤ)
    (M := (Work.CFT.ClassFormation.HnZ G k : Type))
  -- The hypothesis that `|G|` annihilates `H_k(G, ℤ)`, in `nsmul` form.
  have hkill : ∀ g : (Fin r → ℤ), (Fintype.card G) • f g = 0 := fun g =>
    by simpa only [natCast_zsmul] using hT (f g)
  -- The sublattice `|G| ℤ^r` of `ℤ^r` lies in the kernel of `f`.
  let H : Submodule ℤ (Fin r → ℤ) :=
    LinearMap.range (LinearMap.lsmul ℤ (Fin r → ℤ) (Fintype.card G))
  have hH : H ≤ LinearMap.ker f := by
    rintro x ⟨y, rfl⟩
    simp only [LinearMap.mem_ker]
    rw [LinearMap.lsmul_apply, Nat.cast_smul_eq_nsmul, map_nsmul]
    exact hkill y
  -- Hence `f` factors through `ℤ^r ⧸ |G| ℤ^r = ModN ℤ^r |G|`, which is finite.
  refine Finite.of_surjective
    (fun x : ModN (Fin r → ℤ) (Fintype.card G) => (H.liftQ f hH) x) ?_
  intro y
  obtain ⟨g, rfl⟩ := hf y
  refine ⟨H.mkQ g, ?_⟩
  rw [Submodule.mkQ_apply]
  exact Submodule.liftQ_apply H f g

end Work.Tower.Shafarevich.CFT
