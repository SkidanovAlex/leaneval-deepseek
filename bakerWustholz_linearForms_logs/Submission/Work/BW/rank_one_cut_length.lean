import Mathlib
import Submission.Work.BW.rank_one_cut_defs
import Submission.Work.BW.length_quotient_add
import Submission.Work.BW.length_ker_eq_length_coker
import Submission.Work.BW.cut_torsion_length

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Third isomorphism theorem for `M ⧸ (N + P·M)`: it is the quotient of `M ⧸ N` by the image
`P·(M ⧸ N)` of `P·M`. -/
theorem cut_sup_length {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (P : A) (N : Submodule A M) :
    Module.length A (M ⧸ cutSup P N) =
      Module.length A ((M ⧸ N) ⧸ (cutMap P N).range) := by
  have h : Module.length A ((M ⧸ N) ⧸ (cutMap P N).range) =
      Module.length A (M ⧸ cutSup P N) := by
    rw [cutMap_range, cutSup]
    exact (Submodule.quotientQuotientEquivQuotientSup N (cutPM (M := M) P)).length_eq
  exact h.symm

/-- The isomorphism `N ≅ A` identifies `P·N` with `Ideal.span {P}`, whence
`length (N ⧸ P·N) = length (A ⧸ Ideal.span {P})`. -/
theorem cut_quotient_length {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (P : A) (N : Submodule A M) (e : N ≃ₗ[A] A) :
    Module.length A (N ⧸ cutPN P N) = Module.length A (A ⧸ Ideal.span {P}) := by
  have hmap : (cutPN P N).map (e : N →ₗ[A] A) = Ideal.span {P} := by
    rw [cutPN, Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr e.surjective,
      Ideal.smul_eq_mul, Ideal.mul_top]
  exact (Submodule.Quotient.equiv (cutPN P N) (Ideal.span {P}) e hmap).length_eq

/-- **Rank-one cut lemma.** Let `A` be a commutative ring, `M` an `A`-module, `N ⊆ M` a submodule
isomorphic to `A`, and `P : A` a `P`-torsion-free element (`P • y = 0 → y = 0`). Assume the quotient
`M ⧸ N` has finite length. Then cutting `M` by `P` gives the same length as cutting `A` by `P`:
`length (M ⧸ P·M) = length (A ⧸ (P))`.

Proof: put `T := M ⧸ N` (finite length) and `N' := N` (`≅ A`). All of
- `0 → N/(N ⊓ PM) → M/PM → M/(N+PM) → 0`,
- `0 → (N ⊓ PM)/PN → N/PN → N/(N ⊓ PM) → 0`
are exact (`PN ⊆ N ⊓ PM`), and `(N ⊓ PM)/PN ≅ T[P] := ker(P • - : T → T)` (uses `M[P] = 0`,
i.e. `P`-torsion-freeness), while `M/(N+PM) ≅ T ⧸ P·T`. Since `T` has finite length, the kernel and
cokernel of `P • - : T → T` have equal length, so `length (M ⧸ PM) = length (N ⧸ PN) = length (A ⧸ (P))`
(the last because `N ≅ A` identifies `PN` with `Ideal.span {P}`). Use `Module.length_eq_add_of_exact`
throughout. -/
theorem rank_one_cut_length {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (P : A) (N : Submodule A M) (e : N ≃ₗ[A] A)
    (hP : ∀ y : M, P • y = 0 → y = 0)
    (hfin : IsFiniteLength A (M ⧸ N)) :
    Module.length A (M ⧸ (Ideal.span {P} • (⊤ : Submodule A M))) =
      Module.length A (A ⧸ Ideal.span {P}) := by
  -- `(M ⧸ PM)` cut by the submodule `N` and the submodule `N + PM`
  have h1 : Module.length A (M ⧸ cutPM P) =
      Module.length A (M ⧸ cutSup P N) +
        Module.length A (cutSup P N ⧸ (cutPM P).comap (cutSup P N).subtype) :=
    length_quotient_add _ _ le_sup_right
  -- second isomorphism theorem: `(N + PM)/PM ≅ N/(N ∩ PM)`
  have hiso : Module.length A (N ⧸ cutQ P N) =
      Module.length A (cutSup P N ⧸ (cutPM P).comap (cutSup P N).subtype) := by
    have h := (LinearMap.quotientInfEquivSupQuotient N (cutPM (M := M) P)).length_eq
    rw [Submodule.comap_subtype_self, top_inf_eq] at h
    rw [cutQ, cutSup]
    convert h using 2
  -- third isomorphism theorem: `M/(N + PM) ≅ (M ⧸ N) ⧸ P·(M ⧸ N)`
  have h2 : Module.length A (M ⧸ cutSup P N) =
      Module.length A ((M ⧸ N) ⧸ (cutMap P N).range) := cut_sup_length P N
  -- kernel and cokernel of `P·` on the finite-length module `M ⧸ N` have equal length
  have h3 : Module.length A (cutMap P N).ker =
      Module.length A ((M ⧸ N) ⧸ (cutMap P N).range) :=
    length_ker_eq_length_coker (cutMap P N) hfin
  -- `(N ∩ PM)/PN ≅ ker (P·)`
  have h4 : Module.length A (cutQ P N ⧸ cutPNQ P N) = Module.length A (cutMap P N).ker :=
    cut_torsion_length P N hP
  -- `N/PN` is an extension of `N/(N ∩ PM)` by `(N ∩ PM)/PN`
  have h5 : Module.length A (N ⧸ cutPN P N) =
      Module.length A (N ⧸ cutQ P N) + Module.length A (cutQ P N ⧸ cutPNQ P N) :=
    length_quotient_add (cutPN P N) (cutQ P N) (cutPN_le_cutQ P N)
  -- `N ≅ A` identifies `PN` with `Ideal.span {P}`
  have h6 : Module.length A (N ⧸ cutPN P N) = Module.length A (A ⧸ Ideal.span {P}) :=
    cut_quotient_length P N e
  calc Module.length A (M ⧸ cutPM P)
      = Module.length A (M ⧸ cutSup P N) +
          Module.length A (cutSup P N ⧸ (cutPM P).comap (cutSup P N).subtype) := h1
    _ = Module.length A (M ⧸ cutSup P N) + Module.length A (N ⧸ cutQ P N) := by rw [hiso]
    _ = Module.length A ((M ⧸ N) ⧸ (cutMap P N).range) +
          Module.length A (N ⧸ cutQ P N) := by rw [h2]
    _ = Module.length A (cutMap P N).ker + Module.length A (N ⧸ cutQ P N) := by rw [← h3]
    _ = Module.length A (cutQ P N ⧸ cutPNQ P N) + Module.length A (N ⧸ cutQ P N) := by rw [← h4]
    _ = Module.length A (N ⧸ cutQ P N) + Module.length A (cutQ P N ⧸ cutPNQ P N) := add_comm _ _
    _ = Module.length A (N ⧸ cutPN P N) := by rw [← h5]
    _ = Module.length A (A ⧸ Ideal.span {P}) := h6

end Work.BW
