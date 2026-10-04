import Mathlib
import Submission.Work.Diff.STE.B3.VarCoef.pairTermDefs
import Submission.Work.Diff.STE.B3.VarCoef.POp_adjoint_L2re
import Submission.Work.Diff.STE.B3.SymCalcStep7.pairSharpAux
import Submission.Work.Diff.STE.B3.VarCoef.chartTerm_eq_XP

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3.VarCoef

open scoped BigOperators

section Aux

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `POpStar c c' A B k = M_c ∘ (D^*)^k ∘ M_{c'}` preserves smooth `1`-periodic functions. -/
theorem pres_POpStar (A : ι → ι → (ι → ℝ) → ℝ) (B : ι → (ι → ℝ) → ℝ)
    (hA : ∀ a b, ContDiff ℝ (⊤ : ℕ∞) (A a b)) (hAp : ∀ a b, Work.Diff.STE.Periodic1 (A a b))
    (hB : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (B a)) (hBp : ∀ a, Work.Diff.STE.Periodic1 (B a))
    (c c' : (ι → ℝ) → ℝ) (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hcp : Work.Diff.STE.Periodic1 c)
    (hc' : ContDiff ℝ (⊤ : ℕ∞) c') (hc'p : Work.Diff.STE.Periodic1 c') (k : ℕ) :
    Preserves (POpStar c c' A B k) := by
  have hV : Preserves (varLapStarOp A B) := varLapStarOp_preserves A B hA hAp hB hBp
  show Preserves (fun f => mulOp c ((varLapStarOp A B)^[k] (mulOp c' f)))
  exact Preserves.comp (T := fun g => mulOp c ((varLapStarOp A B)^[k] g)) (U := mulOp c')
    (Preserves.comp (T := mulOp c) (U := (varLapStarOp A B)^[k])
      (pres_mulOp c hc hcp) (fun f hf => iterate_smoothPer hV k hf))
    (pres_mulOp c' hc' hc'p)

/-- Additivity of `L2re` over a triple finite sum in the **first** argument. -/
theorem L2re_sum3_fst {κ₁ κ₂ κ₃ : Type*} [Fintype κ₁] [Fintype κ₂] [Fintype κ₃]
    (G : κ₁ → κ₂ → κ₃ → (ι → ℝ) → ℂ) (hG : ∀ i j k, Continuous (G i j k))
    (F : (ι → ℝ) → ℂ) (hF : Continuous F) :
    Work.Diff.STE.L2re (∑ i, ∑ j, ∑ k, G i j k) F
      = ∑ i, ∑ j, ∑ k, Work.Diff.STE.L2re (G i j k) F := by
  rw [show (∑ i, ∑ j, ∑ k, G i j k) = fun x => ∑ i, ∑ j, ∑ k, G i j k x from by
    funext x; simp only [Finset.sum_apply]]
  rw [L2re_finset_sum_fst Finset.univ (fun i => fun x => ∑ j, ∑ k, G i j k x) F
    (fun i _ => continuous_finset_sum_fun Finset.univ _ (fun j _ =>
      continuous_finset_sum_fun Finset.univ _ (fun k _ => hG i j k))) hF]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [L2re_finset_sum_fst Finset.univ (fun j => fun x => ∑ k, G i j k x) F
    (fun j _ => continuous_finset_sum_fun Finset.univ _ (fun k _ => hG i j k)) hF]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact L2re_finset_sum_fst Finset.univ (fun k => G i j k) F (fun k _ => hG i j k) hF

/-- Additivity of `L2re` over a triple finite sum in the **second** argument. -/
theorem L2re_sum3_snd {κ₁ κ₂ κ₃ : Type*} [Fintype κ₁] [Fintype κ₂] [Fintype κ₃]
    (F : (ι → ℝ) → ℂ) (hF : Continuous F)
    (G : κ₁ → κ₂ → κ₃ → (ι → ℝ) → ℂ) (hG : ∀ i j k, Continuous (G i j k)) :
    Work.Diff.STE.L2re F (∑ i, ∑ j, ∑ k, G i j k)
      = ∑ i, ∑ j, ∑ k, Work.Diff.STE.L2re F (G i j k) := by
  rw [show (∑ i, ∑ j, ∑ k, G i j k) = fun x => ∑ i, ∑ j, ∑ k, G i j k x from by
    funext x; simp only [Finset.sum_apply]]
  rw [L2re_finset_sum_snd Finset.univ (fun i => fun x => ∑ j, ∑ k, G i j k x) F
    (fun i _ => continuous_finset_sum_fun Finset.univ _ (fun j _ =>
      continuous_finset_sum_fun Finset.univ _ (fun k _ => hG i j k))) hF]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [L2re_finset_sum_snd Finset.univ (fun j => fun x => ∑ k, G i j k x) F
    (fun j _ => continuous_finset_sum_fun Finset.univ _ (fun k _ => hG i j k)) hF]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact L2re_finset_sum_snd Finset.univ (fun k => G i j k) F (fun k _ => hG i j k) hF

/-- The cutoff sandwich `XOp ψ (cutOp ρ ε) = M_ψ ∘ S_ε ∘ M_ψ` is additive and `ℂ`-homogeneous on
smooth `1`-periodic functions. -/
theorem linSP_XOp_cutOp (ψ : (ι → ℝ) → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψp : Work.Diff.STE.Periodic1 ψ) (ρ : (ι → ℝ) → ℝ) (hρ : ∀ y, ‖ρ y‖ ≤ 1) (ε : ℝ) :
    LinSP (XOp ψ (cutOp ρ ε)) where
  add f g hf hg := by
    show mulOp ψ (cutOp ρ ε (mulOp ψ (f + g)))
        = mulOp ψ (cutOp ρ ε (mulOp ψ f)) + mulOp ψ (cutOp ρ ε (mulOp ψ g))
    have h1 : mulOp ψ (f + g) = mulOp ψ f + mulOp ψ g := by
      funext z; simp only [mulOp, Pi.add_apply]; ring
    rw [h1, (cutOp_isOrd ρ hρ ε).lin.add (mulOp ψ f) (mulOp ψ g)
      (SmoothPer.mulOp' hψ hψp hf) (SmoothPer.mulOp' hψ hψp hg)]
    funext z; simp only [mulOp, Pi.add_apply]; ring
  smul c f hf := by
    show mulOp ψ (cutOp ρ ε (mulOp ψ (c • f))) = c • mulOp ψ (cutOp ρ ε (mulOp ψ f))
    have h1 : mulOp ψ (c • f) = c • mulOp ψ f := by
      funext z; simp only [mulOp, Pi.smul_apply, smul_eq_mul]; ring
    rw [h1, (cutOp_isOrd ρ hρ ε).lin.smul c (mulOp ψ f) (SmoothPer.mulOp' hψ hψp hf)]
    funext z; simp only [mulOp, Pi.smul_apply, smul_eq_mul]; ring

/-- The cutoff sandwich preserves smooth `1`-periodic functions. -/
theorem pres_XOp_cutOp (ψ : (ι → ℝ) → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψp : Work.Diff.STE.Periodic1 ψ) (ρ : (ι → ℝ) → ℝ) (hρ : ∀ y, ‖ρ y‖ ≤ 1) (ε : ℝ) :
    Preserves (XOp ψ (cutOp ρ ε)) :=
  fun f hf => SmoothPer.mulOp' hψ hψp ((cutOp_isOrd ρ hρ ε).pres _ (SmoothPer.mulOp' hψ hψp hf))

/-- The cutoff sandwich distributes over a triple finite sum. -/
theorem XOp_sum3 (ψ : (ι → ℝ) → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψp : Work.Diff.STE.Periodic1 ψ) (ρ : (ι → ℝ) → ℝ) (hρ : ∀ y, ‖ρ y‖ ≤ 1) (ε : ℝ)
    {κ₁ κ₂ κ₃ : Type*} [Fintype κ₁] [Fintype κ₂] [Fintype κ₃]
    (W : κ₁ → κ₂ → κ₃ → (ι → ℝ) → ℂ) (hW : ∀ i j k, SmoothPer (W i j k)) :
    XOp ψ (cutOp ρ ε) (∑ i, ∑ j, ∑ k, W i j k)
      = ∑ i, ∑ j, ∑ k, XOp ψ (cutOp ρ ε) (W i j k) := by
  have hlin := linSP_XOp_cutOp ψ hψ hψp ρ hρ ε
  rw [linSP_map_finset_sum hlin Finset.univ (fun i => ∑ j, ∑ k, W i j k)
    (fun i _ => SmoothPer.finset_sum' Finset.univ (fun j => ∑ k, W i j k)
      (fun j _ => SmoothPer.finset_sum' Finset.univ (fun k => W i j k) (fun k _ => hW i j k)))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [linSP_map_finset_sum hlin Finset.univ (fun j => ∑ k, W i j k)
    (fun j _ => SmoothPer.finset_sum' Finset.univ (fun k => W i j k) (fun k _ => hW i j k))]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact linSP_map_finset_sum hlin Finset.univ (fun k => W i j k) (fun k _ => hW i j k)

/-- `L2re F (XOp ψ S_ε (∑_{i,j,k} W_{ijk})) = ∑_{i,j,k} L2re F (XOp ψ S_ε (W_{ijk}))`. -/
theorem L2re_XOp_sum3 (ψ : (ι → ℝ) → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψp : Work.Diff.STE.Periodic1 ψ) (ρ : (ι → ℝ) → ℝ) (hρ : ∀ y, ‖ρ y‖ ≤ 1) (ε : ℝ)
    {κ₁ κ₂ κ₃ : Type*} [Fintype κ₁] [Fintype κ₂] [Fintype κ₃]
    (F : (ι → ℝ) → ℂ) (hFc : Continuous F)
    (W : κ₁ → κ₂ → κ₃ → (ι → ℝ) → ℂ) (hW : ∀ i j k, SmoothPer (W i j k)) :
    Work.Diff.STE.L2re F (XOp ψ (cutOp ρ ε) (∑ i, ∑ j, ∑ k, W i j k))
      = ∑ i, ∑ j, ∑ k, Work.Diff.STE.L2re F (XOp ψ (cutOp ρ ε) (W i j k)) := by
  have hpres := pres_XOp_cutOp ψ hψ hψp ρ hρ ε
  rw [XOp_sum3 ψ hψ hψp ρ hρ ε W hW]
  exact L2re_sum3_snd F hFc (fun i j k => XOp ψ (cutOp ρ ε) (W i j k))
    (fun i j k => (hpres _ (hW i j k)).continuous)

end Aux

/-- **The decomposition of the scalar pair term.**  The `(α,β)`-pair of the pair estimate is
`L2re (F_α) (X (P^{αβ} U_β)) − L2re (P^{βα} F_α) (X U_β)`, with `X` the cutoff sandwich
`XOp (perPhiR D l) (cutOp ρ ε)` and `P^{αβ} = pairP ce α β` the chart expression of `Qk`.  Writing
`P^{αβ} = Σ_{i,c,d} ptOp ce α β i c d` and using the `L2re`-adjointness
`L2re (ptOp ce β α i c d f) g = L2re f (ptStarOp ce α β i c d g)` of that summand, the pair equals
the sum of the **commutator** terms `L2re F (X (T U)) − L2re F (T (X U))` and the **defect** terms
`L2re F ((T − T^*) (X U))`. -/
theorem pairTerm_decomp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (hρ : ∀ y, ‖ρ y‖ ≤ 1)
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) (l : ι₀)
    (η : (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (ce : Work.Diff.STE.B3.VarCoef.ChartCE (I := I) (M := M) D k l)
    (f u : Work.Diff.STE.Bil (I := I) (M := M))
    (hφ : Work.Diff.STE.B3.VarCoef.SmoothPer
      (fun z => ((Work.Diff.STE.B3.VarCoef.perPhiR (I := I) (M := M) D l z : ℝ) : ℂ)))
    (hF : ∀ a b : Fin (Module.finrank ℝ E), Work.Diff.STE.B3.VarCoef.SmoothPer
      (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l f a b))
    (hU : ∀ a b : Fin (Module.finrank ℝ E), Work.Diff.STE.B3.VarCoef.SmoothPer
      (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l u a b))
    (α β : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) :
    (Work.Diff.STE.L2re (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l f α.1 α.2)
        (Work.Diff.STE.B3.VarCoef.xOpD (I := I) (M := M) D ρ ε l
          (Work.Diff.STE.B3.VarCoef.pairP ce α β
            (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l u β.1 β.2)))
      - Work.Diff.STE.L2re (Work.Diff.STE.B3.VarCoef.pairP ce β α
          (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l f α.1 α.2))
          (Work.Diff.STE.B3.VarCoef.xOpD (I := I) (M := M) D ρ ε l
            (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l u β.1 β.2)))
    = (∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
        ( Work.Diff.STE.L2re (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l f α.1 α.2)
            (Work.Diff.STE.B3.VarCoef.xOpD (I := I) (M := M) D ρ ε l
              (Work.Diff.STE.B3.VarCoef.ptOp ce α β i c d
                (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l u β.1 β.2)))
        - Work.Diff.STE.L2re (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l f α.1 α.2)
            (Work.Diff.STE.B3.VarCoef.ptOp ce α β i c d
              (Work.Diff.STE.B3.VarCoef.xOpD (I := I) (M := M) D ρ ε l
                (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l u β.1 β.2))) ))
      + (∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
        Work.Diff.STE.L2re (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l f α.1 α.2)
          ((Work.Diff.STE.B3.VarCoef.ptOp ce α β i c d
            - Work.Diff.STE.B3.VarCoef.ptStarOp ce α β i c d)
              (Work.Diff.STE.B3.VarCoef.xOpD (I := I) (M := M) D ρ ε l
                (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l u β.1 β.2)))) := by
  classical
  -- Replace `xOpD` by its definition `XOp (perPhiR D l) (cutOp ρ ε)`.
  have hxop : ∀ g : (Fin (Module.finrank ℝ E) → ℝ) → ℂ,
      xOpD (I := I) (M := M) D ρ ε l g
        = XOp (perPhiR (I := I) (M := M) D l) (cutOp ρ ε) g := fun g => rfl
  simp only [hxop]
  -- Abbreviations (all fixed throughout the lemma).
  set ψ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ :=
    perPhiR (I := I) (M := M) D l with hψdef
  set F : (Fin (Module.finrank ℝ E) → ℝ) → ℂ :=
    Work.Diff.STE.B3.perMat (I := I) (M := M) D η l f α.1 α.2 with hFdef
  set U2 : (Fin (Module.finrank ℝ E) → ℝ) → ℂ :=
    Work.Diff.STE.B3.perMat (I := I) (M := M) D η l u β.1 β.2 with hUdef
  set X : Op (Fin (Module.finrank ℝ E)) := XOp ψ (cutOp ρ ε) with hXdef
  -- Smoothness and periodicity of the weight, smoothness of the test functions.
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := by
    have h1 : ContDiff ℝ (⊤ : ℕ∞)
        (fun z : Fin (Module.finrank ℝ E) → ℝ => Complex.re (((ψ z : ℝ) : ℂ))) :=
      Complex.reCLM.contDiff.comp hφ.1
    simpa [Complex.ofReal_re] using h1
  have hψp : Work.Diff.STE.Periodic1 ψ := by
    intro i x
    have h2 := congrArg Complex.re (hφ.2 i x)
    simpa using h2
  have hFsp : SmoothPer F := by rw [hFdef]; exact hF α.1 α.2
  have hUsp : SmoothPer U2 := by rw [hUdef]; exact hU β.1 β.2
  have hXpres : Preserves X := by rw [hXdef]; exact pres_XOp_cutOp ψ hψ hψp ρ hρ ε
  have hXUsp : SmoothPer (X U2) := hXpres U2 hUsp
  -- Smoothness of the individual terms.
  have hTs : ∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E)),
      SmoothPer (ptOp ce α β i c d U2) := fun i c d =>
    pres_POp (ce.A i) (ce.B i) (ce.hA i) (ce.hAp i) (ce.hB i) (ce.hBp i)
      (ce.ci i c d β.1 β.2) (ce.co i α.1 α.2 c d)
      (ce.hci i c d β.1 β.2) (ce.hcip i c d β.1 β.2)
      (ce.hco i α.1 α.2 c d) (ce.hcop i α.1 α.2 c d) k U2 hUsp
  have hTsX : ∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E)),
      SmoothPer (ptOp ce α β i c d (X U2)) := fun i c d =>
    pres_POp (ce.A i) (ce.B i) (ce.hA i) (ce.hAp i) (ce.hB i) (ce.hBp i)
      (ce.ci i c d β.1 β.2) (ce.co i α.1 α.2 c d)
      (ce.hci i c d β.1 β.2) (ce.hcip i c d β.1 β.2)
      (ce.hco i α.1 α.2 c d) (ce.hcop i α.1 α.2 c d) k (X U2) hXUsp
  have hT's : ∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E)),
      SmoothPer (ptOp ce β α i c d F) := fun i c d =>
    pres_POp (ce.A i) (ce.B i) (ce.hA i) (ce.hAp i) (ce.hB i) (ce.hBp i)
      (ce.ci i c d α.1 α.2) (ce.co i β.1 β.2 c d)
      (ce.hci i c d α.1 α.2) (ce.hcip i c d α.1 α.2)
      (ce.hco i β.1 β.2 c d) (ce.hcop i β.1 β.2 c d) k F hFsp
  have hTss : ∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E)),
      SmoothPer (ptStarOp ce α β i c d (X U2)) := fun i c d =>
    pres_POpStar (ce.A i) (fun a => -(ce.B i a)) (ce.hA i) (ce.hAp i)
      (fun a => (ce.hB i a).neg) (fun a => periodic1_neg' (ce.hBp i a))
      (ce.ci i c d α.1 α.2) (ce.co i β.1 β.2 c d)
      (ce.hci i c d α.1 α.2) (ce.hcip i c d α.1 α.2)
      (ce.hco i β.1 β.2 c d) (ce.hcop i β.1 β.2 c d) k (X U2) hXUsp
  -- ## First half: `L2re F (X (pairP ce α β U2)) = Σ_{icd} L2re F (X (T_{icd} U2))`.
  have hL : Work.Diff.STE.L2re F (X (pairP ce α β U2))
      = ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
          Work.Diff.STE.L2re F (X (ptOp ce α β i c d U2)) := by
    have hPU : pairP ce α β U2 = ∑ i, ∑ c, ∑ d, ptOp ce α β i c d U2 := by
      rw [pairP_eq_sum_ptOp]
      funext x
      simp only [Finset.sum_apply]
    rw [hPU]
    exact L2re_XOp_sum3 ψ hψ hψp ρ hρ ε F hFsp.continuous
      (fun i c d => ptOp ce α β i c d U2) hTs
  -- ## Second half: `L2re (pairP ce β α F) (X U2) = Σ_{icd} L2re F (T^*_{icd} (X U2))`.
  have hR : Work.Diff.STE.L2re (pairP ce β α F) (X U2)
      = ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
          Work.Diff.STE.L2re F (ptStarOp ce α β i c d (X U2)) := by
    have hPF : pairP ce β α F = ∑ i, ∑ c, ∑ d, ptOp ce β α i c d F := by
      rw [pairP_eq_sum_ptOp]
      funext x
      simp only [Finset.sum_apply]
    rw [hPF]
    rw [L2re_sum3_fst (fun i c d => ptOp ce β α i c d F)
      (fun i c d => (hT's i c d).continuous) (X U2) hXUsp.continuous]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun c _ =>
      Finset.sum_congr rfl (fun d _ => ?_)))
    exact POp_adjoint_L2re (A := ce.A i) (B := ce.B i) (c := ce.ci i c d α.1 α.2)
      (c' := ce.co i β.1 β.2 c d) k (ce.hA i) (ce.hAp i) (ce.hB i) (ce.hBp i)
      (ce.hci i c d α.1 α.2) (ce.hcip i c d α.1 α.2)
      (ce.hco i β.1 β.2 c d) (ce.hcop i β.1 β.2 c d) F (X U2) hFsp hXUsp
  -- ## The defect sum, term by term.
  have hthird : (∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
        Work.Diff.STE.L2re F ((ptOp ce α β i c d - ptStarOp ce α β i c d) (X U2)))
      = ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
          (Work.Diff.STE.L2re F (ptOp ce α β i c d (X U2))
            - Work.Diff.STE.L2re F (ptStarOp ce α β i c d (X U2))) := by
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun c _ =>
      Finset.sum_congr rfl (fun d _ => ?_)))
    exact Work.Diff.STE.B3.SymCalcStep7.L2re_sub_snd' hFsp.continuous (hTsX i c d).continuous
      (hTss i c d).continuous
  -- ## Distribution of the subtractions over the sums.
  have hAB : (∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
        (Work.Diff.STE.L2re F (X (ptOp ce α β i c d U2))
          - Work.Diff.STE.L2re F (ptOp ce α β i c d (X U2))))
      = (∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
          Work.Diff.STE.L2re F (X (ptOp ce α β i c d U2)))
        - (∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
          Work.Diff.STE.L2re F (ptOp ce α β i c d (X U2))) := by
    simp only [Finset.sum_sub_distrib]
  have hBD : (∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
        (Work.Diff.STE.L2re F (ptOp ce α β i c d (X U2))
          - Work.Diff.STE.L2re F (ptStarOp ce α β i c d (X U2))))
      = (∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
          Work.Diff.STE.L2re F (ptOp ce α β i c d (X U2)))
        - (∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
          Work.Diff.STE.L2re F (ptStarOp ce α β i c d (X U2))) := by
    simp only [Finset.sum_sub_distrib]
  rw [hL, hR, hthird, hAB, hBD]
  ring

end Work.Diff.STE.B3.VarCoef
