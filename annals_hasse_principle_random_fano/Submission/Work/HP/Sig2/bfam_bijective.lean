import Mathlib
import Submission.Work.HP.Sig2.LatStepDefs

namespace Work.HP.Sig2

/-- Splitting a linear combination over `Fin 1 ⊕ Fin (R-1)` into the `u`-part and the
`v`-part: this is just `Fintype.sum_sum_type` together with the definition of `famZ`. -/
private lemma sum_famZ_split {R : ℕ} (u : Fin R → ℤ) (v : Fin (R - 1) → (Fin R → ℤ))
    (g : Fin 1 ⊕ Fin (R - 1) → ℤ) :
    (∑ k, g k • famZ u v k) = g (Sum.inl 0) • u + ∑ i, g (Sum.inr i) • v i := by
  rw [Fintype.sum_sum_type]
  simp only [famZ_inl, famZ_inr]
  congr 1
  exact Fin.sum_univ_one _

/-- The coordinate interchange `((Fin 1 ⊕ Fin (R-1)) → ℤ) ≃ ℤ × (Fin (R-1) → ℤ)`
is a bijection. -/
private lemma sumArrow_prod_bijective {R : ℕ} :
    Function.Bijective (fun g : Fin 1 ⊕ Fin (R - 1) → ℤ =>
      (g (Sum.inl 0), fun i => g (Sum.inr i))) := by
  constructor
  · intro g h hgh
    have h1 : g (Sum.inl 0) = h (Sum.inl 0) := by
      have := congrArg Prod.fst hgh; simpa using this
    have h2 : (fun i => g (Sum.inr i)) = (fun i => h (Sum.inr i)) := by
      have := congrArg Prod.snd hgh; simpa using this
    funext k
    cases k with
    | inl i => rw [Subsingleton.elim i 0]; exact h1
    | inr i => exact congrFun h2 i
  · intro c
    refine ⟨Sum.elim (fun _ : Fin 1 => c.1) c.2, ?_⟩
    simp

/-- Precomposition with the index equivalence `idxEquiv R hR` is a bijection on
coefficient vectors. -/
private lemma precomp_idxEquiv_bijective {R : ℕ} (hR : 1 ≤ R) :
    Function.Bijective (fun x : Fin R → ℤ =>
      fun k : Fin 1 ⊕ Fin (R - 1) => x ((idxEquiv R hR) k)) := by
  constructor
  · intro x y hxy
    funext j
    have := congrFun hxy ((idxEquiv R hR).symm j)
    simpa using this
  · intro g
    refine ⟨fun j => g ((idxEquiv R hR).symm j), ?_⟩
    funext k
    simp

/-- Reindexing a linear combination along an equivalence does not change the composite
map: `∑ j, x j • F (e.symm j) = ∑ k, x (e k) • F k`. -/
private lemma sum_reindex_bfam {R : ℕ} (hR : 1 ≤ R) (u : Fin R → ℤ)
    (v : Fin (R - 1) → (Fin R → ℤ)) (x : Fin R → ℤ) :
    (∑ j, x j • Work.HP.Sig2.bfam hR u v j)
      = ∑ k, x ((idxEquiv R hR) k) • famZ u v k := by
  simpa [bfam] using (Equiv.sum_comp (idxEquiv R hR)
    (fun j => x j • famZ u v ((idxEquiv R hR).symm j))).symm

theorem bfam_bijective {R : ℕ} (hR : 1 ≤ R) (u : Fin R → ℤ) (v : Fin (R - 1) → (Fin R → ℤ))
    (hbij : Function.Bijective (fun c : ℤ × (Fin (R - 1) → ℤ) =>
      c.1 • u + ∑ i, c.2 i • v i)) :
    Function.Bijective (fun x : Fin R → ℤ => ∑ j, x j • Work.HP.Sig2.bfam hR u v j) := by
  -- The hypothesis is bijectivity of the coefficient map for the family `famZ`.
  have hbase : Function.Bijective (fun g : Fin 1 ⊕ Fin (R - 1) → ℤ => ∑ k, g k • famZ u v k) := by
    have hcomp : (fun g : Fin 1 ⊕ Fin (R - 1) → ℤ => ∑ k, g k • famZ u v k)
        = (fun c : ℤ × (Fin (R - 1) → ℤ) => c.1 • u + ∑ i, c.2 i • v i) ∘
          (fun g : Fin 1 ⊕ Fin (R - 1) → ℤ => (g (Sum.inl 0), fun i => g (Sum.inr i))) := by
      funext g
      simp only [Function.comp_apply]
      exact sum_famZ_split u v g
    rw [hcomp]
    exact hbij.comp sumArrow_prod_bijective
  -- `bfam` is `famZ` reindexed along `idxEquiv`, so the target map is `hbase` composed with a
  -- bijection.
  have hfun : (fun x : Fin R → ℤ => ∑ j, x j • Work.HP.Sig2.bfam hR u v j)
      = (fun g : Fin 1 ⊕ Fin (R - 1) → ℤ => ∑ k, g k • famZ u v k) ∘
        (fun x : Fin R → ℤ => fun k : Fin 1 ⊕ Fin (R - 1) => x ((idxEquiv R hR) k)) := by
    funext x
    simp only [Function.comp_apply]
    exact sum_reindex_bfam hR u v x
  rw [hfun]
  exact hbase.comp (precomp_idxEquiv_bijective hR)

end Work.HP.Sig2
