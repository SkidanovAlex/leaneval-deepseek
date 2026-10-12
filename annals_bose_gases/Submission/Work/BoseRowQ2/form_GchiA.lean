import ChallengeDeps
import Submission.Work.BoseRowQ2.maskSharpCore
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseRowQ2/form_GchiA.lean` — the masked-coordinate identity for `GchiA`

This module proves the quadratic-form identity behind the dictionary of
`maskSharpCore`:

    ⟨u, GchiA u⟩ = ⟨w, Mc w⟩ ,   w = wfun u ,

i.e. the matrix `GchiA` of the localised `Σ_j Q_{L,j} χ_Λ² Q_{L,j}` in the θ-frame acts on the
masked coordinates `w_i = f_L i · ⟨g_i, u⟩` exactly through the lattice kernel `Mc`.

The two halves are the elementary expansions

* `GchiA_quad`: `Σ_{l,l'} u_l (GchiA)_{l l'} u_{l'}
   = Σ_{s,s' ∈ excited} f_L s f_L s' χ̂²(s'−s) · ⟨g_{s'},u⟩ ⟨g_s,u⟩`
  (the θ-frame coefficients `Σ_l g_{s'} l u_l = ⟨g_{s'},u⟩`),
* `wfun_quad`: `Σ_{i,j} w_i w_j Mc_{i j}
   = Σ_{s,s' ∈ excited} (f_L s ⟨g_s,u⟩)(f_L s' ⟨g_{s'},u⟩) Mc_{s s'}`,

together with the lattice pin `hatChiSq_sub_eq_Mc` (valid on the labels with `f_L ≠ 0`, which is
the regime recorded by the hypothesis `hN`) and the symmetry `Mc_symm`.

Nothing here is analytic: the content is the finite reindexing, the pin of the kernel at the
supported labels, and the case split on the vanishing of `f_L`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseRowQ2

open Work.BoseB4 Work.BoseB7 Work.BoseBoxFock Work.BoseBoxFix Work.UBB Work.BoseRowsFS

set_option maxHeartbeats 800000

variable {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v} {fc fu : Work.BoseBoxFix.LowCut}

/-! ## 1. Elementary finite-sum lemmas -/

/-- **The mode-sum of a rank-one product.**  For a scalar `A`, the double mode sum of
`u l · (A · a l · b l') · u l'` factors as `A` times the two `gram`-pairings. -/
lemma sum_sum_quad_factor {m : ℕ} (A : ℝ) (u a b : Fin m → ℝ) :
    (∑ l : Fin m, ∑ l', u l * (A * (a l * b l')) * u l')
      = A * ((∑ l, a l * u l) * (∑ l', b l' * u l')) := by
  rw [show (∑ l : Fin m, ∑ l', u l * (A * (a l * b l')) * u l')
        = ∑ l : Fin m, ∑ l', (A * (a l * b l')) * (u l * u l') from
      Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => by ring]
  have h1 : (∑ l : Fin m, ∑ l', (A * (a l * b l')) * (u l * u l'))
      = ∑ l : Fin m, ∑ l', (A * (a l * u l)) * (b l' * u l') :=
    Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => by ring
  rw [h1, ← Finset.sum_mul_sum, ← Finset.mul_sum]
  ring

/-- **Reordering a four-index sum** so that the two `Finset`-restricted indices come first. -/
lemma quad_sum_comm {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] {γ₁ γ₂ : Type*}
    (s₁ : Finset γ₁) (s₂ : Finset γ₂) (F : ι₁ → ι₂ → γ₁ → γ₂ → ℝ) :
    (∑ l : ι₁, ∑ l' : ι₂, ∑ s ∈ s₁, ∑ s' ∈ s₂, F l l' s s')
      = ∑ s ∈ s₁, ∑ s' ∈ s₂, ∑ l : ι₁, ∑ l' : ι₂, F l l' s s' := by
  calc (∑ l : ι₁, ∑ l' : ι₂, ∑ s ∈ s₁, ∑ s' ∈ s₂, F l l' s s')
      = ∑ l : ι₁, ∑ s ∈ s₁, ∑ l' : ι₂, ∑ s' ∈ s₂, F l l' s s' :=
        Finset.sum_congr rfl fun l _ => Finset.sum_comm
    _ = ∑ s ∈ s₁, ∑ l : ι₁, ∑ l' : ι₂, ∑ s' ∈ s₂, F l l' s s' :=
        Finset.sum_comm
    _ = ∑ s ∈ s₁, ∑ l : ι₁, ∑ s' ∈ s₂, ∑ l' : ι₂, F l l' s s' :=
        Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun l _ => Finset.sum_comm
    _ = ∑ s ∈ s₁, ∑ s' ∈ s₂, ∑ l : ι₁, ∑ l' : ι₂, F l l' s s' :=
        Finset.sum_congr rfl fun s _ => Finset.sum_comm

/-! ## 2. The quadratic form of `GchiA` in the θ-frame -/

/-- **`⟨u, GchiA u⟩` in the `θ`-frame.**  The `χ̂²`-kernel of `GchiA` pairs the
`g`-coordinates of `u` directly:
`Σ_{l,l'} u_l (GchiA)_{l l'} u_{l'}
 = Σ_{s,s' ∈ excited} f_L s f_L s' χ̂²(s'−s) · ⟨g_{s'},u⟩ ⟨g_s,u⟩`. -/
lemma GchiA_quad (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) (u : Fin (HM μ).m → ℝ) :
    (∑ l : Fin (HM μ).m, ∑ l' : Fin (HM μ).m,
        u l * GchiA (v := v) (h := h) (fc := fc) (fu := fu) HM μ l l' * u l')
      = ∑ s ∈ excited (Lab (HM μ).N), ∑ s' ∈ excited (Lab (HM μ).N),
            ((honE v h fc fu HM μ).fL s * (honE v h fc fu HM μ).fL s'
              * (honE v h fc fu HM μ).hatChiSq (s' - s))
              * (gcoord HM μ u s' * gcoord HM μ u s) := by
  simp only [GchiA]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [quad_sum_comm]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => ?_
  rw [sum_sum_quad_factor]
  simp only [gcoord, gram]

/-! ## 3. The quadratic form of `Mc` on the masked coordinates -/

/-- **`⟨w, Mc w⟩` in the `θ`-frame.**  The masked coordinates
`w_i = f_L i ⟨g_i,u⟩` (zero off the excited labels) reduce the lattice double sum to the excited
labels. -/
lemma wfun_quad (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) (u : Fin (HM μ).m → ℝ) :
    (∑ i : Lab (HM μ).N, ∑ j : Lab (HM μ).N,
        wfun (v := v) (h := h) (fc := fc) (fu := fu) HM μ u i
          * wfun (v := v) (h := h) (fc := fc) (fu := fu) HM μ u j
          * Mc (HM μ).N i j)
      = ∑ s ∈ excited (Lab (HM μ).N), ∑ s' ∈ excited (Lab (HM μ).N),
            ((honE v h fc fu HM μ).fL s * gcoord HM μ u s)
              * ((honE v h fc fu HM μ).fL s' * gcoord HM μ u s')
              * Mc (HM μ).N s s' := by
  rw [← Finset.sum_subset (Finset.subset_univ (excited (Lab (HM μ).N)))
        (fun i _ hi => ?_)]
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [← Finset.sum_subset (Finset.subset_univ (excited (Lab (HM μ).N)))
          (fun j _ hj => ?_)]
    · refine Finset.sum_congr rfl fun j hj => ?_
      simp only [wfun, if_pos hi, if_pos hj]
    · simp only [wfun, if_neg hj]; ring
  · refine Finset.sum_eq_zero fun j _ => ?_
    simp only [wfun, if_neg hi]; ring

/-! ## 4. The identity -/

theorem form_GchiA {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v} {fc fu : Work.BoseBoxFix.LowCut}
    (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ) (μ : ℝ) (hμ : 0 < μ)
    (hav : 0 < _root_.BoseGases.a v)
    (hN : 2 * Work.BoseRowQ2.RowGchiMaskRowAux.honCutRad v μ / Real.pi ≤ ((HM μ).N : ℝ))
    (u : Fin (HM μ).m → ℝ) :
    (∑ l : Fin (HM μ).m, ∑ l' : Fin (HM μ).m,
        u l * Work.BoseRowQ2.GchiA (v := v) (h := h) (fc := fc) (fu := fu) HM μ l l' * u l')
      = ∑ i : Work.BoseBoxFock.Lab (HM μ).N, ∑ j : Work.BoseBoxFock.Lab (HM μ).N,
          Work.BoseRowQ2.wfun (v := v) (h := h) (fc := fc) (fu := fu) HM μ u i
            * Work.BoseRowQ2.wfun (v := v) (h := h) (fc := fc) (fu := fu) HM μ u j
            * Work.BoseRowQ2.Mc (HM μ).N i j := by
  rw [GchiA_quad HM μ u, wfun_quad (v := v) (h := h) (fc := fc) (fu := fu) HM μ u]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => ?_
  by_cases hs0 : (honE v h fc fu HM μ).fL s = 0
  · rw [hs0]; ring
  by_cases hs'0 : (honE v h fc fu HM μ).fL s' = 0
  · rw [hs'0]; ring
  · rw [Work.BoseRowQ2.hatChiSq_sub_eq_Mc HM μ hμ hav hN s' s hs'0 hs0, Work.BoseRowQ2.Mc_symm]
    ring

end Work.BoseRowQ2
