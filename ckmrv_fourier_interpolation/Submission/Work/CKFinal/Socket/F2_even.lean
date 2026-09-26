import Mathlib
import Submission.Work.CKFinal.Socket.Construction

noncomputable section

open UpperHalfPlane
open scoped Topology Manifold

namespace Work.CKFinal
namespace Socket

/-!
# Evenness of the socket layer `F₂` in the radius

`F₂ ℓ d hd r τ` depends on `r` only through the layer `layerFn`, the window charts (whose
evenness is the axiom `chartFun_even` of `windowChart_data`) and the Gaussian
`gaussTerm σ r = exp(π i σ r²)`; the socket regions `U0`, `W1`, `Wm1` do not involve `r` at all.
All of these are functions of `r²`, hence even.
-/

/-- `sinSq (-r) = sinSq r`. -/
lemma sinSq_neg_socket (r : ℝ) : Work.Asymptotics.sinSq (-r) = Work.Asymptotics.sinSq r := by
  have hsq : (((-r : ℝ)) : ℂ) ^ 2 = ((r : ℝ) : ℂ) ^ 2 := by
    rw [Complex.ofReal_neg, neg_sq]
  simp only [Work.Asymptotics.sinSq, hsq]

lemma layerLow_neg_socket (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : UpperHalfPlane)
    (s : ℝ) :
    Work.Asymptotics.layerLow ℓ d τ (-s) = Work.Asymptotics.layerLow ℓ d τ s := by
  have hsq : (((-s : ℝ)) : ℂ) ^ 2 = ((s : ℝ) : ℂ) ^ 2 := by
    rw [Complex.ofReal_neg, neg_sq]
  simp only [Work.Asymptotics.layerLow, Work.Asymptotics.sinSq, hsq]

lemma layerTrunc_neg_socket (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ)
    (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : UpperHalfPlane) (s : ℝ) :
    Work.Asymptotics.layerTrunc G ℓ d τ (-s) = Work.Asymptotics.layerTrunc G ℓ d τ s := by
  have hsq : (((-s : ℝ)) : ℂ) ^ 2 = ((s : ℝ) : ℂ) ^ 2 := by
    rw [Complex.ofReal_neg, neg_sq]
  simp only [Work.Asymptotics.layerTrunc, Work.Asymptotics.sinSq, hsq]

lemma highPart_neg_socket (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ) (τ : UpperHalfPlane)
    (s : ℝ) :
    Work.Asymptotics.highPart G τ (-s) = Work.Asymptotics.highPart G τ s := by
  simp only [Work.Asymptotics.highPart, neg_sq]

lemma paperLayer_neg_socket (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ)
    (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : UpperHalfPlane) (s : ℝ) :
    Work.Asymptotics.paperLayer G ℓ d τ (-s) = Work.Asymptotics.paperLayer G ℓ d τ s := by
  simp only [Work.Asymptotics.paperLayer]
  rw [layerLow_neg_socket, layerTrunc_neg_socket, highPart_neg_socket]

/-- The layer `layerFn` is even in the radius. -/
lemma layerFn_neg (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (r : ℝ) (τ : UpperHalfPlane) :
    layerFn ℓ d (-r) τ = layerFn ℓ d r τ := by
  simpa only [layerFn] using paperLayer_neg_socket (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r

/-- The Gaussian `gaussTerm τ r = exp(π i τ r²)` is even in the radius. -/
lemma gaussTerm_neg_socket (τ : UpperHalfPlane) (r : ℝ) :
    Work.Kernels.gaussTerm τ (-r) = Work.Kernels.gaussTerm τ r := by
  have hsq : (((-r : ℝ)) : ℂ) ^ 2 = ((r : ℝ) : ℂ) ^ 2 := by
    rw [Complex.ofReal_neg, neg_sq]
  simp only [Work.Kernels.gaussTerm, hsq]

/-- The window-chart value is even in the radius. -/
lemma chartVal_neg (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (r : ℝ) (τ : UpperHalfPlane) (h : τ ∈ W1 ℓ d hd) :
    chartVal ℓ d hd (-r) τ h = chartVal ℓ d hd r τ h := by
  obtain ⟨s, hs, hb⟩ := mem_W1.mp h
  rw [← chartVal_spec ℓ d hd (-r) h s hs hb, chartFun_even ℓ d hd s hs r τ,
    chartVal_spec ℓ d hd r h s hs hb]

/-- Away from `U0 ∪ W1`, `G` is just the layer. -/
lemma G_of_not_mem (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (r : ℝ) {τ : UpperHalfPlane} (h0 : τ ∉ U0) (h1 : τ ∉ W1 ℓ d hd) :
    G ℓ d hd r τ = layerFn ℓ d r τ := by
  classical
  rw [G, dif_neg h0, dif_neg h1]

/-- The glued function `G` is even in the radius. -/
lemma G_neg (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (r : ℝ) (τ : UpperHalfPlane) : G ℓ d hd (-r) τ = G ℓ d hd r τ := by
  classical
  by_cases h0 : τ ∈ U0
  · rw [G_of_mem_U0 ℓ d hd (-r) h0, G_of_mem_U0 ℓ d hd r h0, layerFn_neg]
  · by_cases h1 : τ ∈ W1 ℓ d hd
    · rw [G_of_mem_W1 ℓ d hd (-r) h1, G_of_mem_W1 ℓ d hd r h1,
        chartVal_neg ℓ d hd r τ h1]
    · rw [G_of_not_mem ℓ d hd (-r) h0 h1, G_of_not_mem ℓ d hd r h0 h1, layerFn_neg]

theorem F2_even (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (r : ℝ) (τ : UpperHalfPlane) :
    Work.CKFinal.Socket.F2 ℓ d hd (-r) τ = Work.CKFinal.Socket.F2 ℓ d hd r τ := by
  classical
  by_cases h : τ ∈ Wm1 ℓ d hd
  · rw [F2_of_mem_Wm1 ℓ d hd (-r) h, F2_of_mem_Wm1 ℓ d hd r h]
    have hfun : (fun σ : UpperHalfPlane => Work.Kernels.gaussTerm σ (-r))
        = fun σ : UpperHalfPlane => Work.Kernels.gaussTerm σ r :=
      funext fun σ => gaussTerm_neg_socket σ r
    rw [G_neg ℓ d hd r ((1 : ℝ) +ᵥ τ), G_neg ℓ d hd r ((2 : ℝ) +ᵥ τ), hfun]
  · rw [F2_of_not_mem_Wm1 ℓ d hd (-r) h, F2_of_not_mem_Wm1 ℓ d hd r h,
      G_neg ℓ d hd r τ]

end Socket
end Work.CKFinal
