import Mathlib
import Submission.Work.HP.DetLOrth.Defs

namespace Work.HP.DetLOrth

set_option autoImplicit false

/-- A primitive (saturated) `K ⊆ ℤ^ι` is a direct summand: it has a `ℤ`-basis extending to one of
`ℤ^ι`.  Route: `Submodule.smithNormalForm (Pi.basisFun ℤ ι) K` gives `bM`, `bN`, `f`, `a` with
`(bN i : ι → ℤ) = a i • bM (f i)`; saturation forces `a i = ±1` (write `bM (f i) = ∑ c j • bN j`,
then `1 = c i * a i`), so `K = span {bM (f i)}` and one may take `p j := j ∈ Set.range f`. -/
theorem exists_adapted_basis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Submodule ℤ (ι → ℤ)) (hK : Work.HP.IsPrimLat K) :
    ∃ (b : Module.Basis ι ℤ (ι → ℤ)) (p : ι → Prop),
      K = Submodule.span ℤ (Set.range fun i : {i // p i} => (b i.1 : ι → ℤ)) := by
  -- Smith normal form of `K` inside `ℤ^ι`: there are bases `bM` of `ℤ^ι` and `bN` of `K`,
  -- an embedding `f : Fin n ↪ ι` and scalars `a i` with `bN i = a i • bM (f i)`.
  obtain ⟨n, snf⟩ := K.smithNormalForm (Pi.basisFun ℤ ι)
  -- The `a i` are nonzero because `bN i ≠ 0`.
  have hai : ∀ i, snf.a i ≠ 0 := by
    intro i h0
    refine snf.bN.ne_zero i (Subtype.ext ?_)
    simp [snf.snf i, h0]
  -- `bN` spans `K` (it is a basis of `K`), transported to `ℤ^ι`.
  have hbN_span : K = Submodule.span ℤ (Set.range fun i : Fin n => (snf.bN i : ι → ℤ)) := by
    have h2 : Submodule.map K.subtype ⊤ = K := by
      rw [Submodule.map_top]; exact Submodule.range_subtype K
    calc K = Submodule.map K.subtype ⊤ := h2.symm
      _ = Submodule.map K.subtype (Submodule.span ℤ (Set.range snf.bN)) := by
            rw [Module.Basis.span_eq]
      _ = Submodule.span ℤ (K.subtype '' Set.range snf.bN) := Submodule.map_span K.subtype _
      _ = Submodule.span ℤ (Set.range fun i : Fin n => (snf.bN i : ι → ℤ)) := by
            rw [← Set.range_comp]; rfl
  -- `span {bN i} ≤ span {bM (f i)}` since `bN i = a i • bM (f i)`.
  have hbN_le : Submodule.span ℤ (Set.range fun i : Fin n => (snf.bN i : ι → ℤ))
      ≤ Submodule.span ℤ (Set.range fun i : Fin n => (snf.bM (snf.f i) : ι → ℤ)) := by
    apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    show (snf.bN i : ι → ℤ) ∈
      Submodule.span ℤ (Set.range fun i : Fin n => (snf.bM (snf.f i) : ι → ℤ))
    rw [snf.snf i]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hle : K ≤ Submodule.span ℤ (Set.range fun i : Fin n => (snf.bM (snf.f i) : ι → ℤ)) :=
    hbN_span.trans_le hbN_le
  -- Conversely each `bM (f i)` lies in `K` by saturation.
  have hge : Submodule.span ℤ (Set.range fun i : Fin n => (snf.bM (snf.f i) : ι → ℤ)) ≤ K := by
    apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    show (snf.bM (snf.f i) : ι → ℤ) ∈ K
    exact hK (snf.bM (snf.f i)) (snf.a i) (hai i) (by rw [← snf.snf i]; exact (snf.bN i).2)
  have key : K = Submodule.span ℤ (Set.range fun i : Fin n => (snf.bM (snf.f i) : ι → ℤ)) :=
    le_antisymm hle hge
  -- Reindex the spanning family `bM ∘ f` by the subset `Set.range f ⊆ ι`.
  have hspan_eq : Submodule.span ℤ (Set.range fun i : Fin n => (snf.bM (snf.f i) : ι → ℤ))
      = Submodule.span ℤ
          (Set.range fun i : {i // i ∈ Set.range (snf.f : Fin n → ι)} => (snf.bM i.1 : ι → ℤ)) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro x ⟨i, rfl⟩
      show (snf.bM (snf.f i) : ι → ℤ) ∈ _
      exact Submodule.subset_span ⟨⟨snf.f i, Set.mem_range_self i⟩, rfl⟩
    · apply Submodule.span_le.mpr
      rintro x ⟨⟨j, hj⟩, rfl⟩
      obtain ⟨i, hi⟩ := hj
      show (snf.bM j : ι → ℤ) ∈ _
      rw [← hi]
      exact Submodule.subset_span ⟨i, rfl⟩
  exact ⟨snf.bM, fun j => j ∈ Set.range (snf.f : Fin n → ι), key.trans hspan_eq⟩

end Work.HP.DetLOrth
