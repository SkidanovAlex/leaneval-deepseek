/-
  annals_wilkies_conjecture, AREA E3, frame step: a self-contained copy of the one-variable
  line-derivative lemma used by `Work.WilE3.Frame.frame_derivs_vanish`.

  `Work.WilE3.Frame.iteratedDeriv_line_eq_zero` is the same statement, proved in its own module on
  top of `Work.WilE3.Frame.IterLineAux` and `Work.WilE3.Frame.IterLineShift.opWord_shift_iterate`.
  This module duplicates the (small, purely auxiliary) `edir`-calculus, under names prefixed with
  `fla_`, so that `frame_derivs_vanish` does not depend on those two modules: the auxiliary file
  `IterLineAux` and the module `curve_chain_rule` (needed by `partial_curve_eq_Vword`) both declare
  `Work.WilE3.Frame.edir_congr`, so no module may import both chains.  The one piece that is *not*
  taken over is `opWord_shift_iterate`, which is proved here (`flaOpWord_shift_iterate`).
-/
import Mathlib
import Submission.Work.WilE3.Frame.Setup
import Submission.Work.WilE3.Frame.finRange_take_drop_decomp
import Submission.Work.WilE3.Frame.mem_take_finRange_lt

namespace Work.WilE3.Frame

set_option autoImplicit false
open Classical Topology
open WilkiesDesign.E
open scoped ContDiff

noncomputable section

variable {k : ℕ}

noncomputable def flaOpWord (m : Fin k → ℕ) (G : (Fin k → ℂ) → ℂ) : (Fin k → ℂ) → ℂ :=
  (List.finRange k).foldr (fun l H => (edir l)^[m l] H) G

/-- At a differentiability point the coordinate partial `edir l` is the Fréchet derivative
evaluated on the `l`-th coordinate vector. -/
lemma fla_edir_eq_fderiv (G : (Fin k → ℂ) → ℂ) (u : Fin k → ℂ) (l : Fin k)
    (hG : DifferentiableAt ℂ G u) :
    edir l G u = fderiv ℂ G u (Pi.single l 1) := by
  have hφ : HasDerivAt (fun s : ℂ => u + s • (Pi.single l (1:ℂ) : Fin k → ℂ))
      (Pi.single l (1:ℂ)) 0 := by
    simpa using (hasDerivAt_id (0:ℂ)).smul_const
      (Pi.single l (1:ℂ) : Fin k → ℂ) |>.const_add u
  have hF : HasFDerivAt G (fderiv ℂ G u)
      (u + (0:ℂ) • (Pi.single l (1:ℂ) : Fin k → ℂ)) := by
    simpa using hG.hasFDerivAt
  exact (hF.comp_hasDerivAt 0 hφ).deriv

/-- Near an analyticity point, `edir l G` agrees with the Fréchet derivative evaluated on the
`l`-th coordinate vector. -/
lemma fla_edir_eventuallyEq (G : (Fin k → ℂ) → ℂ) (p : Fin k → ℂ) (l : Fin k)
    (hG : AnalyticAt ℂ G p) :
    edir l G =ᶠ[𝓝 p] (fun u => fderiv ℂ G u (Pi.single l (1:ℂ) : Fin k → ℂ)) := by
  filter_upwards [hG.eventually_analyticAt] with u hu
  exact fla_edir_eq_fderiv G u l hu.differentiableAt

/-- Analyticity is preserved by the coordinate partial derivative. -/
lemma fla_analyticAt_edir (G : (Fin k → ℂ) → ℂ) (p : Fin k → ℂ) (l : Fin k)
    (hG : AnalyticAt ℂ G p) : AnalyticAt ℂ (edir l G) p := by
  refine (analyticAt_congr (fla_edir_eventuallyEq G p l hG)).mpr ?_
  have h : AnalyticAt ℂ (fderiv ℂ G) p := hG.fderiv
  exact (ContinuousLinearMap.apply ℂ ℂ (Pi.single l (1:ℂ) : Fin k → ℂ)).analyticAt _ |>.comp h

/-- `edir l` respects eventual equality. -/
lemma fla_edir_congr {G H : (Fin k → ℂ) → ℂ} {p : Fin k → ℂ} (l : Fin k)
    (h : G =ᶠ[𝓝 p] H) : edir l G =ᶠ[𝓝 p] edir l H := by
  filter_upwards [h.eventuallyEq_nhds] with u hu
  have hh : Filter.Tendsto (fun t : ℂ => u + t • (Pi.single l (1:ℂ) : Fin k → ℂ)) (𝓝 0)
      (𝓝 ((fun t : ℂ => u + t • (Pi.single l (1:ℂ) : Fin k → ℂ)) 0)) :=
    (by fun_prop : Continuous fun t : ℂ => u + t • (Pi.single l (1:ℂ) : Fin k → ℂ)).continuousAt
  rw [show (fun t : ℂ => u + t • (Pi.single l (1:ℂ) : Fin k → ℂ)) 0 = u from by simp] at hh
  exact (hu.comp_tendsto hh).deriv_eq

/-- Mixed partial derivatives commute on analytic functions. -/
lemma fla_edir_comm (G : (Fin k → ℂ) → ℂ) (p : Fin k → ℂ) (i j : Fin k)
    (hG : AnalyticAt ℂ G p) :
    edir i (edir j G) =ᶠ[𝓝 p] edir j (edir i G) := by
  filter_upwards [hG.eventually_analyticAt] with u hu
  have hfi : DifferentiableAt ℂ (fderiv ℂ G) u := hu.fderiv.differentiableAt
  have hevj := fla_edir_eventuallyEq G u j hu
  have hevi := fla_edir_eventuallyEq G u i hu
  have hd1 : DifferentiableAt ℂ (fun v => (fderiv ℂ G v) (Pi.single j (1:ℂ) : Fin k → ℂ)) u :=
    hfi.clm_apply (differentiableAt_const _)
  have hd2 : DifferentiableAt ℂ (fun v => (fderiv ℂ G v) (Pi.single i (1:ℂ) : Fin k → ℂ)) u :=
    hfi.clm_apply (differentiableAt_const _)
  have hdj : DifferentiableAt ℂ (edir j G) u := hevj.differentiableAt_iff.mpr hd1
  have hdi : DifferentiableAt ℂ (edir i G) u := hevi.differentiableAt_iff.mpr hd2
  rw [fla_edir_eq_fderiv (edir j G) u i hdj, fla_edir_eq_fderiv (edir i G) u j hdi]
  rw [hevj.fderiv_eq, hevi.fderiv_eq]
  have hclmj : fderiv ℂ (fun y => fderiv ℂ G y (Pi.single j (1:ℂ) : Fin k → ℂ)) u
      = (fderiv ℂ (fderiv ℂ G) u).flip (Pi.single j (1:ℂ) : Fin k → ℂ) := by
    rw [fderiv_clm_apply hfi (differentiableAt_const (c := (Pi.single j (1:ℂ) : Fin k → ℂ)))]
    simp
  have hclmi : fderiv ℂ (fun y => fderiv ℂ G y (Pi.single i (1:ℂ) : Fin k → ℂ)) u
      = (fderiv ℂ (fderiv ℂ G) u).flip (Pi.single i (1:ℂ) : Fin k → ℂ) := by
    rw [fderiv_clm_apply hfi (differentiableAt_const (c := (Pi.single i (1:ℂ) : Fin k → ℂ)))]
    simp
  rw [hclmj, hclmi, ContinuousLinearMap.flip_apply, ContinuousLinearMap.flip_apply]
  exact (hu.contDiffAt (n := ω)).isSymmSndFDerivAt (by simp) |>.eq (Pi.single i 1) (Pi.single j 1)

/-- Iterated coordinate partial derivatives of an analytic function are analytic. -/
lemma fla_analyticAt_edir_iterate {p : Fin k → ℂ} {X : (Fin k → ℂ) → ℂ} (hX : AnalyticAt ℂ X p)
    (l : Fin k) (a : ℕ) : AnalyticAt ℂ ((edir l)^[a] X) p := by
  induction a with
  | zero => simpa using hX
  | succ a ih => rw [Function.iterate_succ_apply']; exact fla_analyticAt_edir _ p l ih

lemma fla_edir_iterate_congr {p : Fin k → ℂ} {G H : (Fin k → ℂ) → ℂ} (l : Fin k) (a : ℕ)
    (h : G =ᶠ[𝓝 p] H) : (edir l)^[a] G =ᶠ[𝓝 p] (edir l)^[a] H := by
  induction a with
  | zero => simpa using h
  | succ a ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
                 exact fla_edir_congr l ih

/-- One `edir b` can be pulled past an iterate of another coordinate partial. -/
lemma fla_edir_pull {p : Fin k → ℂ} {X : (Fin k → ℂ) → ℂ} (hX : AnalyticAt ℂ X p)
    (b l : Fin k) (c : ℕ) :
    edir b ((edir l)^[c] X) =ᶠ[𝓝 p] (edir l)^[c] (edir b X) := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact (fla_edir_comm ((edir l)^[c] X) p b l (fla_analyticAt_edir_iterate hX l c)).trans
      (fla_edir_congr l ih)

/-- Iterates of two coordinate partials commute on analytic functions. -/
lemma fla_edir_iterate_comm {p : Fin k → ℂ} {X : (Fin k → ℂ) → ℂ} (hX : AnalyticAt ℂ X p)
    (b l : Fin k) (a c : ℕ) :
    (edir b)^[a] ((edir l)^[c] X) =ᶠ[𝓝 p] (edir l)^[c] ((edir b)^[a] X) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact (fla_edir_congr b ih).trans (fla_edir_pull (fla_analyticAt_edir_iterate hX b a) b l c)

/-- A right fold of coordinate partials sends analytic functions to analytic functions. -/
lemma fla_analyticAt_foldr {p : Fin k → ℂ} {F : (Fin k → ℂ) → ℂ} (hF : AnalyticAt ℂ F p)
    (L : List (Fin k)) (m : Fin k → ℕ) :
    AnalyticAt ℂ (L.foldr (fun j H => (edir j)^[m j] H) F) p := by
  induction L with
  | nil => simpa using hF
  | cons b t ih => rw [List.foldr_cons]; exact fla_analyticAt_edir_iterate ih b (m b)

/-- The zero multi-index gives the identity ordered-partial operator. -/
lemma fla_opWord_zero {k : ℕ} (F : (Fin k → ℂ) → ℂ) : flaOpWord (0 : Fin k → ℕ) F = F := by
  simp only [flaOpWord, Pi.zero_apply]
  induction (List.finRange k) with
  | nil => rfl
  | cons b t ih => simpa using ih

/-- Only the `l`-th exponent matters for a fold over a list avoiding `l`. -/
lemma fla_foldr_update_eq {L : List (Fin k)} {l : Fin k} (hl : l ∉ L)
    (m : Fin k → ℕ) (c : ℕ) (F : (Fin k → ℂ) → ℂ) :
    L.foldr (fun j H => (edir j)^[(Function.update m l (m l + c)) j] H) F
      = L.foldr (fun j H => (edir j)^[m j] H) F := by
  induction L with
  | nil => simp
  | cons b t ih =>
    rw [List.foldr_cons, List.foldr_cons]
    have hbl : b ≠ l := fun h => hl (by rw [← h]; exact List.mem_cons_self)
    rw [Function.update_of_ne hbl]
    exact congrArg (fun X => (edir b)^[m b] X) (ih (fun h => hl (List.mem_cons_of_mem b h)))

/-- Increasing one coordinate of a multi-index by one increases its total order by one. -/
lemma fla_sum_update_add_one {m : Fin k → ℕ} (l : Fin k) :
    (∑ i, Function.update m l (m l + 1) i) = (∑ i, m i) + 1 := by
  have hfun : Function.update m l (m l + 1)
      = fun i => m i + (Pi.single l 1 : Fin k → ℕ) i := by
    funext i; by_cases h : i = l <;> simp [Function.update, Pi.single, h]
  rw [hfun, Finset.sum_add_distrib]
  congr 1
  simp [Pi.single_apply]

/-- The Fréchet derivative in coordinates. -/
lemma fla_fderiv_eq_sum (G : (Fin k → ℂ) → ℂ) (u w : Fin k → ℂ) :
    fderiv ℂ G u w = ∑ l, w l * fderiv ℂ G u (Pi.single l (1:ℂ) : Fin k → ℂ) := by
  have hw : w = ∑ l, w l • (Pi.single l (1:ℂ) : Fin k → ℂ) := by
    funext i; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hw]
  rw [map_sum]
  simp

/-- The derivative of a line through an analyticity point, expressed through the coordinate
partial derivatives. -/
lemma fla_line_deriv (G : (Fin k → ℂ) → ℂ) (p w : Fin k → ℂ) (hG : AnalyticAt ℂ G p) :
    deriv (fun t : ℂ => G (p + t • w)) =ᶠ[𝓝 0]
      (fun t : ℂ => ∑ l, w l * (edir l G) (p + t • w)) := by
  have hc : Continuous fun t : ℂ => p + t • w := by fun_prop
  have htend : Filter.Tendsto (fun t : ℂ => p + t • w) (𝓝 0)
      (𝓝 ((fun t : ℂ => p + t • w) 0)) := hc.continuousAt
  rw [show (fun t : ℂ => p + t • w) 0 = p from by simp] at htend
  filter_upwards [htend hG.eventually_analyticAt] with t ht
  have hdiff : DifferentiableAt ℂ G (p + t • w) := ht.differentiableAt
  have hφ : HasDerivAt (fun t : ℂ => p + t • w) w t := by
    simpa using (hasDerivAt_id t).smul_const w |>.const_add p
  have hF : HasFDerivAt G (fderiv ℂ G (p + t • w)) (p + t • w) := hdiff.hasFDerivAt
  have h1 : deriv (fun t : ℂ => G (p + t • w)) t = fderiv ℂ G (p + t • w) w :=
    (hF.comp_hasDerivAt t hφ).deriv
  rw [h1, fla_fderiv_eq_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [fla_edir_eq_fderiv G (p + t • w) l hdiff]

/-- Linearity of `iteratedDeriv` for the sum of coordinate-partial terms along a line. -/
lemma fla_iteratedDeriv_sum_line (n : ℕ) (w : Fin k → ℂ) (p : Fin k → ℂ)
    (G : Fin k → (Fin k → ℂ) → ℂ) (hG : ∀ l, AnalyticAt ℂ (G l) p) :
    iteratedDeriv n (fun t : ℂ => ∑ l, w l * (G l) (p + t • w)) 0
      = ∑ l, w l * iteratedDeriv n (fun t : ℂ => (G l) (p + t • w)) 0 := by
  have hfun : (fun t : ℂ => ∑ l, w l * (G l) (p + t • w))
      = (∑ l : Fin k, fun t : ℂ => w l * (G l) (p + t • w)) := by
    ext t; simp [Finset.sum_apply]
  rw [hfun, iteratedDeriv_sum (f := fun l t => w l * (G l) (p + t • w)) ?_]
  · refine Finset.sum_congr rfl (fun l _ => ?_)
    exact iteratedDeriv_const_mul_field (w l) (fun t : ℂ => (G l) (p + t • w))
  · intro l _
    have h2 : AnalyticAt ℂ (fun t : ℂ => (G l) (p + t • w)) 0 :=
      (hG l).comp_of_eq (by fun_prop) (by simp)
    exact (contDiffAt_const (c := w l)).mul h2.contDiffAt

/-- Folding coordinate partials over a list preserves eventual equality of the argument. -/
lemma fla_foldr_eventuallyEq {L : List (Fin k)} {X Y : (Fin k → ℂ) → ℂ} {p : Fin k → ℂ}
    (m : Fin k → ℕ) (h : X =ᶠ[𝓝 p] Y) :
    L.foldr (fun j H => (edir j)^[m j] H) X =ᶠ[𝓝 p]
      L.foldr (fun j H => (edir j)^[m j] H) Y := by
  induction L with
  | nil => simpa using h
  | cons b t ih =>
      rw [List.foldr_cons, List.foldr_cons]
      exact fla_edir_iterate_congr b (m b) ih

/-- `(edir l)^[c]` commutes with a fold over a list of coordinates avoiding `l`. -/
lemma fla_foldr_edir_pull {L : List (Fin k)} {l : Fin k} (hl : l ∉ L)
    (m : Fin k → ℕ) (F : (Fin k → ℂ) → ℂ) (p : Fin k → ℂ) (hF : AnalyticAt ℂ F p) (c : ℕ) :
    L.foldr (fun j H => (edir j)^[m j] H) ((edir l)^[c] F) =ᶠ[𝓝 p]
      (edir l)^[c] (L.foldr (fun j H => (edir j)^[m j] H) F) := by
  induction L with
  | nil => simp
  | cons b t ih =>
      rw [List.foldr_cons, List.foldr_cons]
      have ht : l ∉ t := fun h => hl (List.mem_cons_of_mem b h)
      have hY : AnalyticAt ℂ (t.foldr (fun j H => (edir j)^[m j] H) F) p :=
        fla_analyticAt_foldr hF t m
      exact (fla_edir_iterate_congr b (m b) (ih ht)).trans
        (fla_edir_iterate_comm hY b l (m b) c)

/-- **The shift identity for ordered-partial words.**  `c` extra `edir l`-derivatives of `F` are
absorbed into the `l`-th exponent of the word `flaOpWord m`. -/
theorem flaOpWord_shift_iterate (F : (Fin k → ℂ) → ℂ) (p : Fin k → ℂ)
    (hF : AnalyticAt ℂ F p) (m : Fin k → ℕ) (l : Fin k) (c : ℕ) :
    flaOpWord m ((edir l)^[c] F) p = flaOpWord (Function.update m l (m l + c)) F p := by
  obtain ⟨hsplit, hlB0⟩ := finRange_take_drop_decomp l
  set A : List (Fin k) := (List.finRange k).take l.val with hA
  set B : List (Fin k) := (List.finRange k).drop (l.val + 1) with hB
  have hsplit' : List.finRange k = A ++ l :: B := by rw [hA, hB]; exact hsplit
  have hlB : l ∉ B := by rw [hB]; exact hlB0
  have hlA : l ∉ A := by
    rw [hA]
    exact fun hmem => absurd (mem_take_finRange_lt l hmem) (lt_irrefl _)
  have hRHS : flaOpWord (Function.update m l (m l + c)) F
      = A.foldr (fun j H => (edir j)^[m j] H)
          ((edir l)^[m l + c] (B.foldr (fun j H => (edir j)^[m j] H) F)) := by
    rw [flaOpWord, hsplit', List.foldr_append, List.foldr_cons, Function.update_self]
    rw [fla_foldr_update_eq hlB m c F]
    exact fla_foldr_update_eq hlA m c _
  have step1 : flaOpWord m ((edir l)^[c] F)
      =ᶠ[𝓝 p] A.foldr (fun j H => (edir j)^[m j] H)
          ((edir l)^[m l] (B.foldr (fun j H => (edir j)^[m j] H) ((edir l)^[c] F))) := by
    rw [flaOpWord, hsplit', List.foldr_append, List.foldr_cons]
  have hB' : B.foldr (fun j H => (edir j)^[m j] H) ((edir l)^[c] F)
      =ᶠ[𝓝 p] (edir l)^[c] (B.foldr (fun j H => (edir j)^[m j] H) F) :=
    fla_foldr_edir_pull hlB m F p hF c
  have hinner : (edir l)^[m l] (B.foldr (fun j H => (edir j)^[m j] H) ((edir l)^[c] F))
      =ᶠ[𝓝 p] (edir l)^[m l + c] (B.foldr (fun j H => (edir j)^[m j] H) F) := by
    simpa only [Function.iterate_add_apply] using fla_edir_iterate_congr l (m l) hB'
  have step2 : A.foldr (fun j H => (edir j)^[m j] H)
        ((edir l)^[m l] (B.foldr (fun j H => (edir j)^[m j] H) ((edir l)^[c] F)))
      =ᶠ[𝓝 p] A.foldr (fun j H => (edir j)^[m j] H)
        ((edir l)^[m l + c] (B.foldr (fun j H => (edir j)^[m j] H) F)) :=
    fla_foldr_eventuallyEq m hinner
  have hmain : flaOpWord m ((edir l)^[c] F)
      =ᶠ[𝓝 p] flaOpWord (Function.update m l (m l + c)) F := by
    rw [hRHS]
    exact step1.trans step2
  exact hmain.eq_of_nhds

/-- **Ordered partials control the derivatives along lines** (the statement of
`Work.WilE3.Frame.iteratedDeriv_line_eq_zero`, established here without importing that module). -/
theorem frame_line_deriv {k : ℕ} (F : (Fin k → ℂ) → ℂ) (p w : Fin k → ℂ) (n : ℕ)
    (hF : AnalyticAt ℂ F p)
    (hpar : ∀ m : Fin k → ℕ, (∑ i, m i) ≤ n →
      ((List.finRange k).foldr (fun l G => (edir l)^[m l] G) F) p = 0) :
    iteratedDeriv n (fun t : ℂ => F (p + t • w)) 0 = 0 := by
  have hpar' : ∀ m : Fin k → ℕ, (∑ i, m i) ≤ n → flaOpWord m F p = 0 :=
    fun m hm => by simpa only [flaOpWord] using hpar m hm
  have key : ∀ n : ℕ, ∀ (F : (Fin k → ℂ) → ℂ) (p w : Fin k → ℂ), AnalyticAt ℂ F p →
      (∀ m : Fin k → ℕ, (∑ i, m i) ≤ n → flaOpWord m F p = 0) →
      iteratedDeriv n (fun t : ℂ => F (p + t • w)) 0 = 0 := by
    intro n
    induction n with
    | zero =>
      intro F p w hF hpar
      rw [iteratedDeriv_zero]
      have h1 : flaOpWord (0 : Fin k → ℕ) F p = 0 := hpar 0 (by simp)
      rw [fla_opWord_zero F] at h1
      simpa using h1
    | succ n ih =>
      intro F p w hF hpar
      rw [iteratedDeriv_succ']
      rw [Filter.EventuallyEq.iteratedDeriv_eq n (fla_line_deriv F p w hF)]
      rw [fla_iteratedDeriv_sum_line n w p (fun l => edir l F)
        (fun l => fla_analyticAt_edir F p l hF)]
      refine Finset.sum_eq_zero (fun l _ => ?_)
      have hterm : iteratedDeriv n (fun t : ℂ => (edir l F) (p + t • w)) 0 = 0 :=
        ih (edir l F) p w (fla_analyticAt_edir F p l hF) (by
          intro m hm
          have hsh := flaOpWord_shift_iterate F p hF m l 1
          rw [Function.iterate_one] at hsh
          rw [hsh]
          exact hpar (Function.update m l (m l + 1)) (by
            rw [fla_sum_update_add_one l]; omega))
      rw [hterm, mul_zero]
  exact key n F p w hF hpar'

end

end Work.WilE3.Frame
