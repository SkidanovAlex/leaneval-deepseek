import Mathlib
import Submission.Work.DSG4a.Present
import Submission.Work.DSG4a.mem_splitIdeal_presentMk
import Submission.Work.DSG4a.solSet_span_eq_baseChange

namespace Work.DSG4a

universe u

/-- **Flat descent of unimodularity for a presented module.**  If the element `1 ⊗ e` of
the base change `present D ⊗[A] A' = A'^m ⧸ im (D_{A'})` is unimodular over a flat
`A`-algebra `A'`, then the unit of `A'` lies in the image of the splitting ideal of `e`
under `algebraMap A A'`.

The proof uses the description of the splitting ideal of a presented element
(`mem_splitIdeal_presentMk`): `splitIdeal A (presentMk D e)` is the set of values
`⟪w, e⟫` for `w` in the solution set `solSet D` of the transposed system.  Flat base change
(`solSet_span_eq_baseChange`) realises every solution over `A'` as an `A'`-linear
combination of base changed solutions over `A`; applying the functional `x ↦ ⟪x, e'⟫`
turns the relation `⟪w', e'⟫ = 1` into an expression of `1` as an `A'`-linear combination
of elements of the image ideal. -/
theorem one_mem_splitIdeal_map_present {A A' : Type u} [CommRing A] [CommRing A'] [Algebra A A']
    {m n : ℕ} (D : Fin m → Fin n → A) (e : Fin m → A) (hflat : Module.Flat A A')
    (h : Module.IsUnimodular A' (Work.DSG4a.presentMk (fun i j => algebraMap A A' (D i j))
      (fun i => algebraMap A A' (e i)))) :
    (1 : A') ∈ (Work.DSG4a.splitIdeal A (Work.DSG4a.presentMk D e)).map (algebraMap A A') := by
  -- Unimodularity over `A'` exhibits a coordinate vector `w'` with `⟪w', e'⟫ = 1`.
  obtain ⟨w', hw', hwe'⟩ :=
    (mem_splitIdeal_presentMk (fun i j => algebraMap A A' (D i j))
      (fun i => algebraMap A A' (e i)) (1 : A')).mp (one_mem_splitIdeal_iff.mpr h)
  -- Flat base change expresses `w'` as an `A'`-linear combination of the base changed
  -- solutions of the transposed system over `A`.
  rw [← solSet_span_eq_baseChange D hflat] at hw'
  -- The functional `x ↦ ⟪x, e'⟫` sends every base changed solution into the ideal, whence
  -- it sends their span into the ideal as well.
  have hS : ((fun w : Fin m → A => fun i => algebraMap A A' (w i)) ''
      (solSet D : Set (Fin m → A))) ⊆
      Submodule.comap (ofCoord (fun i => algebraMap A A' (e i)))
        ((splitIdeal A (presentMk D e)).map (algebraMap A A')) := fun s hs => by
    obtain ⟨w, hw, rfl⟩ := hs
    dsimp only
    change ofCoord (fun i => algebraMap A A' (e i)) (fun i => algebraMap A A' (w i)) ∈
      Ideal.map (algebraMap A A') (splitIdeal A (presentMk D e))
    rw [ofCoord_apply, dot_comm, dot_algebraMap]
    exact Ideal.mem_map_of_mem (algebraMap A A')
      ((mem_splitIdeal_presentMk D e (dot w e)).mpr ⟨w, hw, rfl⟩)
  have key : ofCoord (fun i => algebraMap A A' (e i)) w' ∈
      (splitIdeal A (presentMk D e)).map (algebraMap A A') :=
    (Submodule.span_le.mpr hS) hw'
  have hval : ofCoord (fun i => algebraMap A A' (e i)) w' = 1 := by
    rw [ofCoord_apply, dot_comm]; exact hwe'
  rw [hval] at key
  exact key

end Work.DSG4a
