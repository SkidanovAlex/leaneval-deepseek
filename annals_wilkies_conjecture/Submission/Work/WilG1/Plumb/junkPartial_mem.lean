import Mathlib
import Submission.Work.WilG1.Plumb.Imports
import Submission.Work.WilG1.Calc.lt_mem
import Submission.Work.WilG1.Calc.le_mem
import Submission.Work.WilG1.Calc.supBall_mem
import Submission.Work.WilG1.Plumb.DerivDefs
import Submission.Work.WilG1.Plumb.SsetCore
import Submission.Work.WilG1.Plumb.SsetMem

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG1.Plumb

open WilkiesDesign WilkiesConjecture

variable {S : WilkiesDesign.SOMin}

/-! ## 1. The `ε`-`δ` form of the pointwise condition

`epsCond_yuw` replaces the quantifier over a second point `y` (agreeing with `x` off `i`) by
the quantifier over `h = y i - x i`, i.e. by the usual one-variable `ε`-`δ` formulation applied
to the curve `t ↦ f (i.insertNth t (i.removeNth x))`. -/

theorem epsCond_yuw {n : ℕ} (f : (Fin (n + 1) → ℝ) → ℝ) (i : Fin (n + 1))
    (x : Fin (n + 1) → ℝ) (c ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    (∀ y : Fin (n + 1) → ℝ, ∀ u w : ℝ, (∀ j : Fin (n + 1), j ≠ i → y j = x j) →
        (y i - x i) ^ 2 < δ ^ 2 → u = f y → w = f x →
        (u - w - c * (y i - x i)) ^ 2 ≤ ε ^ 2 * (y i - x i) ^ 2)
      ↔ (∀ h : ℝ, |h| < δ →
          |f (i.insertNth (x i + h) (i.removeNth x)) - f (i.insertNth (x i) (i.removeNth x))
            - c * h| ≤ ε * |h|) := by
  have hx0 : f (i.insertNth (x i) (i.removeNth x)) = f x := by
    rw [Fin.insertNth_self_removeNth]
  have key : ∀ t : ℝ,
      i.insertNth (x i + t) (i.removeNth x) = Function.update x i (x i + t) :=
    fun t => Fin.insertNth_removeNth i (x i + t) x
  constructor
  · intro H h hh
    rw [hx0]
    have hlt : x i + h - x i = h := by ring
    have hsq : (x i + h - x i) ^ 2 < δ ^ 2 := by
      have habs := abs_lt.mp hh
      rw [hlt]
      nlinarith [habs.1, habs.2, hδ]
    have hbad : ((i.insertNth (x i + h) (i.removeNth x)) i - x i) ^ 2 < δ ^ 2 := by
      rw [key h, Function.update_self]
      exact hsq
    have hag : ∀ j : Fin (n + 1), j ≠ i →
        (i.insertNth (x i + h) (i.removeNth x)) j = x j := by
      intro j hj
      rw [key h, Function.update_of_ne hj]
    have hres := H (i.insertNth (x i + h) (i.removeNth x))
      (f (i.insertNth (x i + h) (i.removeNth x))) (f x) hag hbad rfl rfl
    have hui : (i.insertNth (x i + h) (i.removeNth x)) i = x i + h := by
      rw [key h, Function.update_self]
    rw [hui, hlt] at hres
    have hres' : (f (i.insertNth (x i + h) (i.removeNth x)) - f x - c * h) ^ 2
        ≤ (ε * h) ^ 2 := by
      calc (f (i.insertNth (x i + h) (i.removeNth x)) - f x - c * h) ^ 2
          ≤ ε ^ 2 * h ^ 2 := hres
        _ = (ε * h) ^ 2 := by ring
    rw [sq_le_sq, abs_mul, abs_of_pos hε] at hres'
    exact hres'
  · intro H y u w hag hbad hu hw
    subst hu
    subst hw
    have hy : y = i.insertNth (x i + (y i - x i)) (i.removeNth x) := by
      rw [key (y i - x i)]
      funext j
      by_cases hj : j = i
      · rw [hj, Function.update_self]
        ring
      · rw [Function.update_of_ne hj]
        exact hag j hj
    have hfy : f y = f (i.insertNth (x i + (y i - x i)) (i.removeNth x)) := congrArg f hy
    have hδ' : |y i - x i| < δ := by
      have h := (sq_lt_sq).mp hbad
      rwa [abs_of_pos hδ] at h
    have hH := H (y i - x i) hδ'
    have hH2 : |f (i.insertNth (x i + (y i - x i)) (i.removeNth x)) - f x - c * (y i - x i)|
        ≤ ε * |y i - x i| := by
      rwa [hx0] at hH
    rw [hfy]
    have h3 : |f (i.insertNth (x i + (y i - x i)) (i.removeNth x)) - f x - c * (y i - x i)|
        ≤ |ε * (y i - x i)| := by
      rw [abs_mul, abs_of_pos hε]
      exact hH2
    have h4 := (sq_le_sq).mpr h3
    calc (f (i.insertNth (x i + (y i - x i)) (i.removeNth x)) - f x - c * (y i - x i)) ^ 2
        ≤ (ε * (y i - x i)) ^ 2 := h4
      _ = ε ^ 2 * (y i - x i) ^ 2 := by ring

/-! ## 2. Coordinates of an assembled point -/

theorem innerSet_asm_iff {N : ℕ} (i : Fin N) (f : (Fin N → ℝ) → ℝ)
    (x : Fin N → ℝ) (c ε δ : ℝ) (y : Fin N → ℝ) (u w : ℝ) :
    asm N x c ε δ y u w ∈ innerSet N i f ↔
      (¬ (∀ j : Fin N, j ≠ i → y j = x j)) ∨
      (¬ ((y i - x i) ^ 2 < δ ^ 2)) ∨
      (¬ (u = f y)) ∨
      (¬ (w = f x)) ∨
      ((u - w - c * (y i - x i)) ^ 2 ≤ ε ^ 2 * (y i - x i) ^ 2) := by
  have hx : (fun j : Fin N => asm N x c ε δ y u w (xIdx N j)) = x := by
    funext j
    simp
  have hy : (fun j : Fin N => asm N x c ε δ y u w (yIdx N j)) = y := by
    funext j
    simp
  rw [mem_innerSet, hx, hy]
  simp only [asm_xIdx, asm_cIdx, asm_eIdx, asm_dIdx, asm_uIdx, asm_wIdx, asm_yIdx]

/-! ## 3. `Sset` is the `ε`-`δ` derivative set -/

theorem Sset_char {n : ℕ} (i : Fin (n + 1)) (f : (Fin (n + 1) → ℝ) → ℝ) :
    Sset (n + 1) i f = {v : Fin ((n+1)+1) → ℝ |
      epsDeriv (fun t : ℝ => f (i.insertNth t (i.removeNth (Fin.init v))))
        ((Fin.init v) i) (v (Fin.last (n + 1)))} := by
  ext v
  have hunf := Sset_unfold_aux (N := n + 1) i f v
  rw [hunf]
  simp only [epsDeriv]
  constructor
  · intro H ε hε
    obtain ⟨δ, hδ0, hδ⟩ := H ε hε
    refine ⟨δ, hδ0, ?_⟩
    have hcond : ∀ y : Fin (n + 1) → ℝ, ∀ u w : ℝ,
        (∀ j : Fin (n + 1), j ≠ i → y j = (Fin.init v) j) →
        (y i - (Fin.init v) i) ^ 2 < δ ^ 2 → u = f y → w = f (Fin.init v) →
        (u - w - (v (Fin.last (n + 1))) * (y i - (Fin.init v) i)) ^ 2
          ≤ ε ^ 2 * (y i - (Fin.init v) i) ^ 2 := by
      intro y u w hag hb hu hw
      have h := hδ y u w
      rw [innerSet_asm_iff] at h
      tauto
    exact (epsCond_yuw f i (Fin.init v) (v (Fin.last (n + 1))) ε δ hε hδ0).mp hcond
  · intro H ε hε
    obtain ⟨δ, hδ0, hδ⟩ := H ε hε
    refine ⟨δ, hδ0, fun y u w => ?_⟩
    rw [innerSet_asm_iff]
    have h := (epsCond_yuw f i (Fin.init v) (v (Fin.last (n + 1))) ε δ hε hδ0).mpr hδ
    have h' := h y u w
    tauto

/-! ## 4. The derivative as a function of the graph -/

theorem deriv_eq_iff_hasDerivAt' {g : ℝ → ℝ} {a c : ℝ} :
    deriv g a = c ↔ HasDerivAt g c a ∨ (c = 0 ∧ ¬ DifferentiableAt ℝ g a) := by
  constructor
  · intro h
    by_cases hd : DifferentiableAt ℝ g a
    · refine Or.inl ?_
      have hh := hd.hasDerivAt
      rwa [h] at hh
    · exact Or.inr ⟨by rw [← h, deriv_zero_of_not_differentiableAt hd], hd⟩
  · rintro (h | ⟨rfl, hd⟩)
    · exact h.deriv
    · exact deriv_zero_of_not_differentiableAt hd

theorem exists_hasDerivAt_iff {g : ℝ → ℝ} {a : ℝ} :
    (∃ c : ℝ, HasDerivAt g c a) ↔ DifferentiableAt ℝ g a := by
  constructor
  · rintro ⟨c, hc⟩
    exact hasDerivAt_deriv_iff.mp (by rw [hc.deriv]; exact hc)
  · intro hd
    exact ⟨deriv g a, hd.hasDerivAt⟩

/-! ## 5. The graph of `junkPartial` -/

theorem graph_eq {n : ℕ} (i : Fin (n + 1)) (f : (Fin (n + 1) → ℝ) → ℝ) :
    graphOf (Work.WilG1.junkPartial i f) =
      Sset (n + 1) i f ∪
        ({v : Fin ((n+1)+1) → ℝ | Fin.init v ∉ projLast (Sset (n + 1) i f)} ∩
         {v : Fin ((n+1)+1) → ℝ | v (Fin.last (n + 1)) = 0}) := by
  ext v
  have hsnoc : Fin.snoc (Fin.init v) (v (Fin.last (n + 1))) = v := Fin.snoc_init_self v
  have hchar : ∀ c : ℝ, (Fin.snoc (Fin.init v) c ∈ Sset (n + 1) i f ↔
      epsDeriv (fun t : ℝ => f (i.insertNth t (i.removeNth (Fin.init v))))
        ((Fin.init v) i) c) := by
    intro c
    rw [Sset_char]
    simp
  have hmemb : v ∈ Sset (n + 1) i f ↔
      epsDeriv (fun t : ℝ => f (i.insertNth t (i.removeNth (Fin.init v))))
        ((Fin.init v) i) (v (Fin.last (n + 1))) := by
    have h := hchar (v (Fin.last (n + 1)))
    rwa [hsnoc] at h
  have hproj : (Fin.init v ∈ projLast (Sset (n + 1) i f)) ↔
      (∃ c : ℝ, epsDeriv (fun t : ℝ => f (i.insertNth t (i.removeNth (Fin.init v))))
        ((Fin.init v) i) c) := by
    rw [projLast, Set.mem_ofPred_eq]
    exact exists_congr fun c => hchar c
  have hiff : (∃ c' : ℝ, HasDerivAt (fun t : ℝ => f (i.insertNth t (i.removeNth (Fin.init v))))
        c' ((Fin.init v) i)) ↔
      (∃ c' : ℝ, epsDeriv (fun t : ℝ => f (i.insertNth t (i.removeNth (Fin.init v))))
        ((Fin.init v) i) c') :=
    exists_congr fun c' => hasDerivAt_iff_epsDeriv
  have key : deriv (fun t : ℝ => f (i.insertNth t (i.removeNth (Fin.init v)))) ((Fin.init v) i)
        = v (Fin.last (n + 1)) ↔
      epsDeriv (fun t : ℝ => f (i.insertNth t (i.removeNth (Fin.init v))))
        ((Fin.init v) i) (v (Fin.last (n + 1))) ∨
      ((¬ (∃ c' : ℝ, epsDeriv (fun t : ℝ => f (i.insertNth t (i.removeNth (Fin.init v))))
        ((Fin.init v) i) c')) ∧ v (Fin.last (n + 1)) = 0) := by
    rw [deriv_eq_iff_hasDerivAt']
    constructor
    · rintro (h | ⟨h0, hd⟩)
      · exact Or.inl (hasDerivAt_iff_epsDeriv.mp h)
      · exact Or.inr ⟨fun hcon => hd (exists_hasDerivAt_iff.mp (hiff.mpr hcon)), h0⟩
    · rintro (h | ⟨hne, h0⟩)
      · exact Or.inl (hasDerivAt_iff_epsDeriv.mpr h)
      · exact Or.inr ⟨h0, fun hd => hne (hiff.mp (exists_hasDerivAt_iff.mpr hd))⟩
  have hjunk : Work.WilG1.junkPartial i f (Fin.init v)
      = deriv (fun t : ℝ => f (i.insertNth t (i.removeNth (Fin.init v)))) ((Fin.init v) i) := rfl
  simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq, graphOf, projLast]
  rw [hmemb]
  rw [show (¬ ∃ t : ℝ, Fin.snoc (Fin.init v) t ∈ Sset (n + 1) i f) ↔
        (¬ ∃ c : ℝ, epsDeriv (fun t : ℝ => f (i.insertNth t (i.removeNth (Fin.init v))))
          ((Fin.init v) i) c) from not_congr hproj]
  rw [show (v (Fin.last (n + 1)) = Work.WilG1.junkPartial i f (Fin.init v)) ↔
        (deriv (fun t : ℝ => f (i.insertNth t (i.removeNth (Fin.init v)))) ((Fin.init v) i)
          = v (Fin.last (n + 1))) from by rw [hjunk]; exact eq_comm]
  exact key

/-! ## 6. The target -/

theorem junkPartial_mem {S : WilkiesDesign.SOMin} {n F D : ℕ} (i : Fin (n + 1))
    (f : (Fin (n + 1) → ℝ) → ℝ) (hf : WilkiesDesign.graphOf f ∈ S.Ω F D (n + 2)) :
    ∃ (a : ℕ) (b : Polynomial ℕ),
      WilkiesDesign.graphOf (Work.WilG1.junkPartial i f) ∈ S.Ω a (b.eval D) (n + 2) := by
  obtain ⟨a, b, hS⟩ := Sset_omega_aux (S := S) (N := n + 1) (F := F) (D := D) i hf
  have hzero : {v : Fin ((n+1)+1) → ℝ | v (Fin.last (n + 1)) = 0} ∈
      S.Ω (n + 2) ((Polynomial.C 1 : Polynomial ℕ).eval D) (n + 2) := by
    have h := S.hyp (n + 2)
      (MvPolynomial.X (Fin.last (n + 1)) : MvPolynomial (Fin (n + 2)) ℝ)
    rw [MvPolynomial.totalDegree_X] at h
    simpa using h
  have hproj : projLast (Sset (n + 1) i f) ∈ S.Ω (a + 1) (b.eval D) (n + 1) := S.proj hS
  have hnot : (projLast (Sset (n + 1) i f))ᶜ ∈ S.Ω (a + 2) (b.eval D) (n + 1) := S.compl hproj
  have hlift : {v : Fin ((n+1)+1) → ℝ | Fin.init v ∈ (projLast (Sset (n + 1) i f))ᶜ} ∈
      S.Ω (a + 3) (b.eval D) (n + 2) := S.prod_right hnot
  have hinter := Work.WilG1.Omega.inter₂ hlift hzero
  have hunion := Work.WilG1.Omega.union₂ hS hinter
  refine ⟨max a (max (a + 3) (n + 2) + 1), b + (b + Polynomial.C 1), ?_⟩
  rw [graph_eq i f]
  simpa using hunion

end Work.WilG1.Plumb
