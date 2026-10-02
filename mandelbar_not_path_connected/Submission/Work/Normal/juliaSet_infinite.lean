import Mathlib
import Submission.Work.Normal.Basic
import Submission.Work.Normal.JuliaBasics
import Submission.Work.Normal.JuliaIterate
import Submission.Work.Normal.unique_preimage_mem_fatou
import Submission.Work.Normal.poly_eval_surjective

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.style.haveILetI false

namespace Work.Normal

/-- The Julia set of a polynomial map of degree at least two is infinite (hence nonempty).

Route.  `JuliaSet f = frontier (FilledJuliaSet f)` is nonempty by `juliaSet_nonempty`.  Suppose
`JuliaSet f` were finite.  The map `g : ↥(JuliaSet f) → ↥(JuliaSet f)`, `g x = ⟨f x, _⟩`, is
surjective (using `poly_eval_surjective` and backward invariance `preimage_juliaSet_subset`) and
hence injective on the finite type; so for `z ∈ JuliaSet f` some iterate `g^[p] z = z` with `p ≥ 1`
(pigeonhole with `Fintype.exists_ne_map_eq_of_card_lt` plus injectivity of `g^[i]`).  For that `p`,
`f^[p]` is a polynomial map of degree `d ^ p ≥ 2` (`isPolynomialMapOfDegree_iterate`) whose fixed
point `z` has the unique preimage `z`: every preimage of `z` under `f^[p]` lies in `JuliaSet f`
(`preimage_iterate_juliaSet_subset`), and `g^[p]` is injective with `g^[p] z = z`.  Then
`unique_preimage_mem_fatou` puts `z` in `FatouSet (f^[p])`, which equals `FatouSet f` by taking
complements in `juliaSet_iterate` — contradicting `z ∈ JuliaSet f`. -/
theorem juliaSet_infinite {d : ℕ} {f : ℂ → ℂ} (hd : 2 ≤ d)
    (hf : IsPolynomialMapOfDegree d f) : (JuliaSet f).Infinite := by
  intro hfin
  haveI : Fintype ↥(JuliaSet f) := hfin.fintype
  -- The map induced by `f` on the Julia set, as a self-map of the (finite) subtype.
  let g : ↥(JuliaSet f) → ↥(JuliaSet f) :=
    fun x => ⟨f x.1, mapsTo_juliaSet hd hf x.2⟩
  -- The value of an iterate of `g` is the corresponding iterate of `f`.
  have hval : ∀ n (x : ↥(JuliaSet f)), (g^[n] x).1 = (f^[n]) x.1 := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact congrArg f (ih x)
  -- `g` is surjective, because `f` is surjective and the Julia set is backward invariant.
  have hgsurj : Function.Surjective g := by
    intro y
    obtain ⟨w, hw⟩ := poly_eval_surjective (by omega : 1 ≤ d) hf y.1
    refine ⟨⟨w, preimage_juliaSet_subset hd hf ?_⟩, ?_⟩
    · rw [Set.mem_preimage, hw]; exact y.2
    · exact Subtype.ext hw
  have hginj : Function.Injective g := Finite.injective_iff_surjective.mpr hgsurj
  obtain ⟨z, hz⟩ := juliaSet_nonempty hd hf
  let Z : ↥(JuliaSet f) := ⟨z, hz⟩
  -- Pigeonhole: on the finite type some positive iterate of `g` fixes `Z`.
  obtain ⟨p, hp, hper⟩ : ∃ p : ℕ, 1 ≤ p ∧ g^[p] Z = Z := by
    obtain ⟨i, j, hij, heq⟩ :=
      Fintype.exists_ne_map_eq_of_card_lt
        (fun i : Fin (Fintype.card ↥(JuliaSet f) + 1) => g^[(i : ℕ)] Z)
        (by rw [Fintype.card_fin]; exact Nat.lt_succ_self _)
    have hne' : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
    rcases lt_or_gt_of_ne hne' with hlt | hlt
    · refine ⟨(j : ℕ) - (i : ℕ), by omega, ?_⟩
      have h1 : g^[(i : ℕ)] Z = g^[(i : ℕ)] (g^[((j : ℕ) - (i : ℕ))] Z) := by
        rw [← Function.iterate_add_apply,
          show (i : ℕ) + ((j : ℕ) - (i : ℕ)) = (j : ℕ) by omega]
        exact heq
      exact (hginj.iterate (i : ℕ) h1).symm
    · refine ⟨(i : ℕ) - (j : ℕ), by omega, ?_⟩
      have h1 : g^[(j : ℕ)] Z = g^[(j : ℕ)] (g^[((i : ℕ) - (j : ℕ))] Z) := by
        rw [← Function.iterate_add_apply,
          show (j : ℕ) + ((i : ℕ) - (j : ℕ)) = (i : ℕ) by omega]
        exact heq.symm
      exact (hginj.iterate (j : ℕ) h1).symm
  have hfixed : (f^[p]) z = z := by
    have h := congrArg Subtype.val hper
    rw [hval p Z] at h
    exact h
  -- `z` is the only preimage of itself under `f^[p]`.
  have huniq : ∀ w : ℂ, (f^[p]) w = z → w = z := by
    intro w hw
    have hwJ : w ∈ JuliaSet f :=
      preimage_iterate_juliaSet_subset hd hf p (by rw [Set.mem_preimage, hw]; exact hz)
    have hgg : (g^[p]) ⟨w, hwJ⟩ = g^[p] Z := by
      apply Subtype.ext
      rw [hval p ⟨w, hwJ⟩, hval p Z, hw, hfixed]
    exact congrArg Subtype.val ((hginj.iterate p) hgg)
  have hiff : ∀ w : ℂ, (f^[p]) w = z ↔ w = z :=
    fun w => ⟨huniq w, fun h => by rw [h]; exact hfixed⟩
  have hdeg : 2 ≤ d ^ p := by
    calc 2 ≤ d := hd
      _ = d ^ 1 := (pow_one d).symm
      _ ≤ d ^ p := Nat.pow_le_pow_right (by omega : 0 < d) hp
  -- `z` is therefore a (superattracting) fixed point of `f^[p]`, hence in its Fatou set,
  -- and the Julia/Fatou sets of `f^[p]` and `f` coincide.
  have hfatoup : z ∈ FatouSet (f^[p]) :=
    unique_preimage_mem_fatou hdeg (isPolynomialMapOfDegree_iterate hf p) hiff
  have hF : FatouSet (f^[p]) = FatouSet f :=
    compl_inj_iff.mp (juliaSet_iterate (by omega : 1 ≤ d) hf hp)
  exact hz (hF ▸ hfatoup)

end Work.Normal
