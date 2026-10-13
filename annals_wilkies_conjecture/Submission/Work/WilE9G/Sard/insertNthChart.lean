import Mathlib

namespace Work.WilE9G.Sard

/-- `Fin.insertNth i · ·` viewed as a continuous linear map `ℝ × (Fin m → ℝ) → (Fin (m+1) → ℝ)`. -/
noncomputable def insertNthCLM (m : ℕ) (i : Fin (m + 1)) :
    (ℝ × (Fin m → ℝ)) →L[ℝ] (Fin (m + 1) → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => Fin.insertNth (α := fun _ => ℝ) i y.1 y.2
      map_add' := by
        intro y z
        exact Fin.insertNth_binop (α := fun _ => ℝ) (fun _ a b => a + b) i y.1 z.1 y.2 z.2
      map_smul' := by
        intro c y
        exact Fin.insertNth_binop (α := fun _ => ℝ) (fun _ a _ => c • a) i y.1 y.1 y.2 y.2 }

/-- The derivative of `q ↦ Fin.insertNth i q.2 (Φ q)` is the insertion of the `ℝ`-component
into the derivative of `Φ`. This is the key computation behind
`surjectiveFderivInsertNthIffAux`. -/
theorem fderivInsertNthApplyAux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : ℕ} (i : Fin (m + 1)) (Φ : E × ℝ → (Fin m → ℝ)) (p : E × ℝ)
    (hΦ : DifferentiableAt ℝ Φ p) (v : E) (s : ℝ) :
    fderiv ℝ (fun q : E × ℝ => Fin.insertNth (α := fun _ => ℝ) i q.2 (Φ q)) p (v, s)
      = Fin.insertNth (α := fun _ => ℝ) i s (fderiv ℝ Φ p (v, s)) := by
  have hΨ : HasFDerivAt (fun q : E × ℝ => (q.2, Φ q))
      ((ContinuousLinearMap.snd ℝ E ℝ).prod (fderiv ℝ Φ p)) p :=
    (ContinuousLinearMap.snd ℝ E ℝ).hasFDerivAt.prodMk hΦ.hasFDerivAt
  have hins : HasFDerivAt (insertNthCLM m i) (insertNthCLM m i)
      ((fun q : E × ℝ => (q.2, Φ q)) p) := (insertNthCLM m i).hasFDerivAt
  have hcomp : HasFDerivAt (insertNthCLM m i ∘ fun q : E × ℝ => (q.2, Φ q))
      ((insertNthCLM m i).comp ((ContinuousLinearMap.snd ℝ E ℝ).prod (fderiv ℝ Φ p))) p :=
    HasFDerivAt.comp (x := p) (f := fun q : E × ℝ => (q.2, Φ q)) hins hΨ
  change (fderiv ℝ (insertNthCLM m i ∘ fun q : E × ℝ => (q.2, Φ q)) p) (v, s) = _
  rw [hcomp.fderiv]
  rfl

/-- The derivative of the partial function `u ↦ Φ (u, p.2)` is obtained from `fderiv Φ p` by
composing with the inclusion `v ↦ (v, 0)`. -/
theorem fderiv_slice_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : ℕ} (Φ : E × ℝ → (Fin m → ℝ)) (p : E × ℝ) (hΦ : DifferentiableAt ℝ Φ p) :
    fderiv ℝ (fun u : E => Φ (u, p.2)) p.1
      = (fderiv ℝ Φ p).comp (ContinuousLinearMap.inl ℝ E ℝ) := by
  have h := HasFDerivAt.comp (x := p.1) (f := fun u : E => (u, p.2))
    hΦ.hasFDerivAt (hasFDerivAt_prodMk_left (𝕜 := ℝ) p.1 p.2)
  exact h.fderiv

theorem surjectiveFderivInsertNthIffAux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : ℕ} (i : Fin (m + 1)) (Φ : E × ℝ → (Fin m → ℝ)) (p : E × ℝ)
    (hΦ : DifferentiableAt ℝ Φ p) :
    Function.Surjective (fderiv ℝ (fun q : E × ℝ => Fin.insertNth (α := fun _ => ℝ) i q.2 (Φ q)) p)
      ↔ Function.Surjective (fderiv ℝ (fun u : E => Φ (u, p.2)) p.1) := by
  have hFval : ∀ (v : E) (s : ℝ),
      fderiv ℝ (fun q : E × ℝ => Fin.insertNth (α := fun _ => ℝ) i q.2 (Φ q)) p (v, s)
        = Fin.insertNth (α := fun _ => ℝ) i s (fderiv ℝ Φ p (v, s)) :=
    fderivInsertNthApplyAux i Φ p hΦ
  have hA := fderiv_slice_eq Φ p hΦ
  have hD0 : ∀ v : E, fderiv ℝ Φ p (v, 0)
      = fderiv ℝ (fun u : E => Φ (u, p.2)) p.1 v := by
    intro v; rw [hA]; rfl
  constructor
  · -- forward: surjectivity of the full derivative forces surjectivity of the slice derivative
    intro hL w
    obtain ⟨q, hq⟩ := hL (Fin.insertNth (α := fun _ => ℝ) i (0 : ℝ) w)
    obtain ⟨v, s⟩ := q
    rw [hFval v s] at hq
    have hs : s = 0 := by
      have h2 := congrFun hq i
      simpa [Fin.insertNth_apply_same] using h2
    subst hs
    refine ⟨v, ?_⟩
    rw [← hD0 v]
    exact (Fin.insertNth_right_injective (α := fun _ => ℝ) (p := i) (0 : ℝ)) hq
  · -- backward: surjectivity of the slice derivative gives surjectivity of the full derivative
    intro hA' y
    obtain ⟨v, hv⟩ := hA' (Fin.removeNth i y - fderiv ℝ Φ p (0, y i))
    refine ⟨(v, y i), ?_⟩
    rw [hFval v (y i)]
    have hsplit : fderiv ℝ Φ p (v, y i)
        = fderiv ℝ Φ p (v, 0) + fderiv ℝ Φ p (0, y i) := by
      have := map_add (fderiv ℝ Φ p) (v, 0) (0, y i)
      simpa using this
    rw [hsplit, hD0 v, hv, sub_add_cancel]
    exact Fin.insertNth_self_removeNth i y

end Work.WilE9G.Sard
