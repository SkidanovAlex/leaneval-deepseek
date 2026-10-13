import Mathlib
import Submission.Work.DSCOH.ChartFree
import Submission.Work.DSCOH.exists_homogeneous_generators

/-!
# The graded free cover of a finitely generated graded module

Let `S = A[X₀,…,X_{n-1}]` (`Poly A n`), let `M` be an `S`-module which is internally graded by
`ℳ : ℕ → Submodule A M` (`DirectSum.Decomposition ℳ`) and on which `S` acts in a graded way
(`SetLike.GradedSMul (homSub A n) ℳ`).  If `M` is finitely generated as an `S`-module, then there
is a graded free `S`-module `F = ⊕_{j : Fin r} S(-d j)` and a *graded* surjection `π : F → M`
(so that the `e`-th piece of `F` is mapped into `ℳ e`), whose kernel is again finitely generated
and carries the induced grading, which is again an internal direct sum.

This is the first step of the resolution argument: `M` is covered by a finite direct sum of shifts
of `S`, and the kernel is handled by descending induction using the long exact sequence of the
chart Čech complexes.

## Main results

* `Work.DSCOH.isInternal_comap_ker` — the kernel of a graded map between internally graded modules
  is internally graded, by the intersections with the pieces of the source.
* `Work.DSCOH.exists_graded_cover` — the graded free cover above.
-/

namespace Work.DSCOH

open DirectSum

/-! ## The kernel of a graded map is internally graded -/

/-- In a direct sum, the `e`-th coordinate of the finite sum `∑ i ∈ s, of i (v i)` is `v e`. -/
private lemma of_sum_apply {ι : Type*} [DecidableEq ι] {N : ι → Type*}
    [∀ i, AddCommMonoid (N i)] {s : Finset ι} (v : (i : ι) → N i) {e : ι} (he : e ∈ s) :
    (∑ i ∈ s, DirectSum.of N i (v i)) e = v e := by
  rw [DFinsupp.finsetSum_apply, Finset.sum_eq_single e]
  · exact DirectSum.of_eq_same e (v e)
  · intro b _ hb
    exact DirectSum.of_eq_of_ne b e (v b) (Ne.symm hb)
  · intro he'; exact absurd he he'

/-- **The kernel of a graded map between internally graded modules is internally graded.**

Let `S : ι → Submodule R X` and `T : ι → Submodule R Y` be internal direct sum decompositions, and
let `π : X →ₗ[R] Y` map the `i`-th piece of `S` into the `i`-th piece of `T`.  Then the kernel of
`π`, graded by the preimages `(S i).comap (LinearMap.ker π).subtype` (i.e. by the intersections
with the pieces of `S`), is again an internal direct sum.

Independence is inherited from `S` (the pieces of the kernel sit inside the pieces of `S`);
spanning uses the *injectivity* of the decomposition of `T`: the decomposition of an element
`x ∈ ker π` along `S` has the property that each of its finitely many components is again killed
by `π`, because their images lie in the independent pieces `T i` and sum to `π x = 0`. -/
theorem isInternal_comap_ker {ι : Type*} [DecidableEq ι]
    {R : Type*} [Ring R] {X Y : Type*} [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y]
    {S : ι → Submodule R X} {T : ι → Submodule R Y}
    (hS : DirectSum.IsInternal S) (hT : DirectSum.IsInternal T)
    (π : X →ₗ[R] Y) (hπ : ∀ i, Submodule.map π (S i) ≤ T i) :
    DirectSum.IsInternal fun i => (S i).comap (LinearMap.ker π).subtype := by
  classical
  set Kf : ι → Submodule R (LinearMap.ker π) :=
    fun i => (S i).comap (LinearMap.ker π).subtype with hKf
  have hmem : ∀ i (x : LinearMap.ker π), x ∈ Kf i ↔ (x : X) ∈ S i := by
    intro i x
    rw [hKf]
    exact Submodule.mem_comap
  refine isInternal_submodule_of_iSupIndep_of_iSup_eq_top ?_ ?_
  · -- Independence is inherited from `S`.
    rw [iSupIndep]
    intro i
    rw [Submodule.disjoint_def]
    intro x hx1 hx2
    have h1 : (x : X) ∈ S i := (hmem i x).mp hx1
    have h2 : (x : X) ∈ ⨆ j, ⨆ (_ : j ≠ i), S j := by
      have hle : (⨆ j, ⨆ (_ : j ≠ i), Kf j) ≤
          Submodule.comap (LinearMap.ker π).subtype (⨆ j, ⨆ (_ : j ≠ i), S j) := by
        refine iSup_le fun j => iSup_le fun hj => ?_
        rw [hKf]
        refine Submodule.comap_mono ?_
        exact le_trans (le_iSup (fun _ : j ≠ i => S j) hj)
          (le_iSup (fun j => ⨆ (_ : j ≠ i), S j) j)
      exact Submodule.mem_comap.mp (hle hx2)
    have hd := Submodule.disjoint_def.mp (hS.submodule_iSupIndep i) (x : X) h1 h2
    exact Subtype.ext hd
  · -- Spanning: decompose along `S` and use that `T` is independent.
    rw [Submodule.eq_top_iff']
    intro x
    obtain ⟨d, hd⟩ : ∃ d, DirectSum.coeAddMonoidHom S d = (x : X) := hS.2 (x : X)
    have hsum : ∑ i ∈ d.support, ((d i : ↥(S i)) : X) = (x : X) := by
      have h := congrArg (fun w => DirectSum.coeAddMonoidHom S w) (DirectSum.sum_support_of d)
      simp only [DirectSum.coeAddMonoidHom_of, map_sum] at h
      rw [hd] at h
      exact h
    have hker : ∀ i, π ((d i : ↥(S i)) : X) = 0 := by
      intro i
      by_cases hi : i ∈ d.support
      · -- The `i`-th component of the decomposition is killed by `π`.
        set z : ⨁ i, ↥(T i) := ∑ i ∈ d.support,
          DirectSum.of (fun i => ↥(T i)) i
            ⟨π ((d i : ↥(S i)) : X), hπ i ⟨(d i : ↥(S i)), (d i).2, rfl⟩⟩ with hz
        have hz0 : z = 0 := by
          apply hT.1
          have hzsum : DirectSum.coeAddMonoidHom T z = 0 := by
            rw [hz, map_sum]
            rw [show (∑ i ∈ d.support, DirectSum.coeAddMonoidHom T
                (DirectSum.of (fun i => ↥(T i)) i
                  ⟨π ((d i : ↥(S i)) : X), hπ i ⟨(d i : ↥(S i)), (d i).2, rfl⟩⟩))
              = ∑ i ∈ d.support, π ((d i : ↥(S i)) : X) from
              Finset.sum_congr rfl fun i _ => DirectSum.coeAddMonoidHom_of T i _]
            rw [← map_sum, hsum]
            exact x.2
          simpa using hzsum
        have hzi : z i = 0 := congrArg (fun w : ⨁ i, ↥(T i) => w i) hz0
        rw [hz, of_sum_apply _ hi] at hzi
        exact congrArg Subtype.val hzi
      · have hdi : d i = 0 := by
          by_contra hne
          exact hi ((DFinsupp.mem_support_iff).mpr hne)
        rw [hdi]
        simp
    have hx : x = ∑ i ∈ d.support, (⟨((d i : ↥(S i)) : X), hker i⟩ : LinearMap.ker π) := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      exact hsum.symm
    rw [hx]
    refine Submodule.sum_mem _ fun i hi => Submodule.mem_iSup_of_mem i ?_
    exact (hmem i _).mpr ((d i).2)

/-! ## The graded free cover -/

theorem exists_graded_cover {A : Type*} [CommRing A] [IsNoetherianRing A] {n : ℕ}
    {M : Type*} [AddCommGroup M] [Module A M] [Module (Poly A n) M] [IsScalarTower A (Poly A n) M]
    (ℳ : ℕ → Submodule A M) [DirectSum.Decomposition ℳ] [SetLike.GradedSMul (homSub A n) ℳ]
    [Module.Finite (Poly A n) M] :
    ∃ (r : ℕ) (d : Fin r → ℕ) (π : (Fin r → Poly A n) →ₗ[Poly A n] M),
      Function.Surjective π ∧
        (∀ e, Submodule.map (π.restrictScalars A) (freeGraded (A := A) (n := n) d e) ≤ ℳ e) ∧
        Module.Finite (Poly A n) (LinearMap.ker π) ∧
        DirectSum.IsInternal (kerGraded (A := A) (n := n) d π) := by
  classical
  -- Finitely many homogeneous generators of `M`.
  obtain ⟨r, g, d, hg, hspan⟩ :=
    exists_homogeneous_generators (A := A) (n := n) (M := M) ℳ
  refine ⟨r, d, freeCover (A := A) (n := n) g, ?_, ?_, ?_, ?_⟩
  · -- The cover is surjective.
    exact freeCover_surjective (A := A) (n := n) hspan
  · -- The cover is graded.
    intro e
    exact freeCover_map_freeGraded_le (A := A) (n := n) ℳ hg e
  · -- The kernel is finitely generated: it is a submodule of the finite free module
    -- `Fin r → S` over the Noetherian ring `S = A[X₀,…,X_{n-1}]`.
    rw [Module.Finite.iff_fg]
    have : IsNoetherianRing (Poly A n) := MvPolynomial.isNoetherianRing
    refine Submodule.FG.of_le (T := ⊤)
      ((Module.Finite.iff_fg (N := (⊤ : Submodule (Poly A n) (Fin r → Poly A n)))).mp
        inferInstance) le_top
  · -- The induced grading on the kernel is an internal direct sum.
    exact isInternal_comap_ker (S := freeGraded (A := A) (n := n) d) (T := ℳ)
      (freeGraded_isInternal (A := A) (n := n) d)
      (DirectSum.Decomposition.isInternal ℳ)
      ((freeCover (A := A) (n := n) g).restrictScalars A)
      (fun e => freeCover_map_freeGraded_le (A := A) (n := n) ℳ hg e)

end Work.DSCOH
