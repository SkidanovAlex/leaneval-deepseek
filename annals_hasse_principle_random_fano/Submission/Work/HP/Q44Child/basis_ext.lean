import Mathlib
import Submission.Work.HP.Q44Child.SuperDefs
import Submission.Work.HP.Q44Child.toE_basis_gram

namespace Work.HP.Q44Child

set_option maxHeartbeats 800000

/-- A primitive (saturated) rank-`2` sublattice `Λ ⊆ ℤ^5` is a direct summand: there is a
`ℤ`-basis `b` of `ℤ^5` whose first two vectors span `Λ`.  The remaining two conditions
(linear independence over `ℝ` of the images `toE (b i)`, and Gram determinant `1`) hold for
*every* `ℤ`-basis of `ℤ^5` (see `toE_basis_gram`), because `b` is unimodular. -/
theorem basis_ext (Λ : Submodule ℤ (Fin 5 → ℤ)) (hΛ : Work.HP.rk Λ = 2)
    (hΛs : Work.HP.IsPrimLat Λ) :
    ∃ b : Module.Basis (Fin 5) ℤ (Fin 5 → ℤ),
      Λ = Submodule.span ℤ (Set.range fun i : Fin 2 => b (Fin.castLE (by norm_num : 2 ≤ 5) i)) ∧
      LinearIndependent ℝ (fun i : Fin 5 => Work.HP.Q44Child.toE (b i)) ∧
      (Matrix.gram ℝ (fun i : Fin 5 => Work.HP.Q44Child.toE (b i))).det = 1 := by
  obtain ⟨n, o, hno, bO, bN, a, ha⟩ :=
    Λ.exists_smith_normal_form_of_le (Pi.basisFun ℤ (Fin 5)) ⊤ le_top
  -- the rank of `Λ` is `2`, so `n = 2`; the ambient module has rank `5`, so `o = 5`.
  have hn : n = 2 := by
    have h1 : Module.finrank ℤ Λ = Fintype.card (Fin n) := Module.finrank_eq_card_basis bN
    rw [Fintype.card_fin] at h1
    have h2 : Module.finrank ℤ Λ = 2 := hΛ
    omega
  have ho : o = 5 := by
    have h1 : Module.finrank ℤ (Fin 5 → ℤ) = Fintype.card (Fin o) :=
      Module.finrank_eq_card_basis (bO.map (LinearEquiv.ofTop ⊤ rfl))
    rw [Fintype.card_fin] at h1
    have h2 : Module.finrank ℤ (Fin 5 → ℤ) = 5 := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    omega
  subst hn
  subst ho
  -- the basis of `ℤ^5` obtained from the Smith-normal-form basis of `⊤`
  let b : Module.Basis (Fin 5) ℤ (Fin 5 → ℤ) := bO.map (LinearEquiv.ofTop ⊤ rfl)
  -- Smith normal form: `bN i = a i • b i`, with `a i ≠ 0`
  have hb : ∀ i : Fin 2, (bN i : Fin 5 → ℤ) = a i • b (Fin.castLE hno i) := by
    intro i
    rw [ha i]
    congr 1
  -- the `bN i` span `Λ`
  have hspan : Λ = Submodule.span ℤ (Set.range fun i : Fin 2 => (bN i : Fin 5 → ℤ)) := by
    have h2 : Submodule.map Λ.subtype ⊤ = Λ := by
      rw [Submodule.map_top]; exact Submodule.range_subtype Λ
    calc Λ = Submodule.map Λ.subtype ⊤ := h2.symm
      _ = Submodule.map Λ.subtype (Submodule.span ℤ (Set.range bN)) := by
            rw [Module.Basis.span_eq]
      _ = Submodule.span ℤ (Λ.subtype '' Set.range bN) := Submodule.map_span Λ.subtype _
      _ = Submodule.span ℤ (Set.range fun i : Fin 2 => (bN i : Fin 5 → ℤ)) := by
            rw [← Set.range_comp]; rfl
  -- `Λ ⊆ span{b 0, b 1}`
  have h1 : Λ ≤ Submodule.span ℤ (Set.range fun i : Fin 2 => b (Fin.castLE hno i)) := by
    rw [hspan]
    apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    show (bN i : Fin 5 → ℤ) ∈ Submodule.span ℤ (Set.range fun i : Fin 2 => b (Fin.castLE hno i))
    rw [hb i]
    exact Submodule.smul_mem _ (a i) (Submodule.subset_span ⟨i, rfl⟩)
  -- `span{b 0, b 1} ⊆ Λ`, using primitivity of `Λ`
  have h2 : Submodule.span ℤ (Set.range fun i : Fin 2 => b (Fin.castLE hno i)) ≤ Λ := by
    apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    have hai : a i ≠ 0 := by
      intro h0
      have h1' : (bN i : Fin 5 → ℤ) = 0 := by rw [hb i, h0, zero_smul]
      exact bN.ne_zero i (Subtype.ext (by simpa using h1'))
    exact hΛs _ (a i) hai (by rw [← hb i]; exact (bN i).2)
  exact ⟨b, le_antisymm h1 h2, (toE_basis_gram b).1, (toE_basis_gram b).2⟩

end Work.HP.Q44Child
