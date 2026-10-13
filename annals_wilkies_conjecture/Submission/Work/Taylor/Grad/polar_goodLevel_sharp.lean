import Mathlib
import Submission.Work.WilE3.Taylor.Grad.PolarDefs
import Submission.Work.WilE3.Taylor.Grad.polarCount_goodLevel
import Submission.Work.WilE3.Taylor.Grad.gradOrderLe
import Submission.Work.WilE3.eaEval_analytic
import Submission.Work.Taylor.Grad.grad_eaEval

/-!
  annals_wilkies_conjecture, AREA Taylor / Grad: the **sharp good-level order bound**.

  From the two unconditional inputs

  * the proved good-level count `Work.WilE3.Taylor.Grad.polarCount_goodLevel`
    (`m ≤ a · K.eval (atomDeg Φ)`), and
  * the one-variable chain-rule order bound `Work.WilE3.Taylor.Grad.gradOrderLe`
    (`n + a ≤ m` for `n` the minimal order of a partial derivative of `Φ` along `γ`),

  the conclusion is that *some* partial derivative `∂ᵢΦ` vanishes to a finite order `n` along `γ`
  with `(D + 1) · n ≤ D · m`, where `D = K.eval (atomDeg Φ)`.

  The argument is entirely elementary once both bounds are in hand: let `n` be the minimal order of
  a partial derivative (it is finite, since otherwise `gradOrderLe` with the numerical bound `m + 1`
  would give the contradiction `m + 1 + a ≤ m`).  Then

  * `gradOrderLe` gives `n + a ≤ m`, hence `n ≤ m - a`;
  * `polarCount_goodLevel` gives `m ≤ a · D`, hence `m ≤ (D + 1) · a`;

  and therefore, multiplying `n ≤ m - a` by `D + 1` and comparing,

  `(D + 1) · n ≤ (D + 1) · (m - a) = (D + 1) · m - (D + 1) · a ≤ (D + 1) · m - m = D · m`.
-/

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
open scoped Topology

namespace Work.Taylor.Grad

theorem polar_goodLevel_sharp (hMB : Work.WilE3.MultiplicityBound) (F : ℕ) :
    ∃ K : Polynomial ℕ, ∀ (k r : ℕ) (c : WilkiesDesign.E.EAChain k r)
      (Φ : WilkiesDesign.E.EAPoly k r) (y : Fin k → ℝ) (γ : ℝ → Fin k → ℝ) (m a : ℕ)
      (i₀ : Fin k),
      k + r ≤ F → AnalyticAt ℝ γ 0 → γ 0 = y → 0 < a → 0 < m →
      analyticOrderAt (fun t : ℝ => γ t - y) 0 = a →
      analyticOrderAt (fun t : ℝ => WilkiesDesign.E.eaEval c Φ (γ t)) 0 = m →
      (∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∀ i : Fin k, i ≠ i₀ →
        WilkiesDesign.E.eaEval c (Work.WilE3.Taylor.polarSys c Φ i₀ i) (γ t) = 0) →
      (¬ ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        (Matrix.of fun i j => WilkiesDesign.E.eaEval c
          (WilkiesDesign.E.eaD c j (Work.WilE3.Taylor.polarSys c Φ i₀ i)) (γ t)).det = 0) →
      ∃ (i : Fin k) (n : ℕ),
        analyticOrderAt (fun t : ℝ => WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c i Φ) (γ t)) 0
          = n ∧
        (K.eval (WilkiesDesign.E.atomDeg Φ) + 1) * n ≤ K.eval (WilkiesDesign.E.atomDeg Φ) * m := by
  obtain ⟨K, hK⟩ := Work.WilE3.Taylor.Grad.polarCount_goodLevel hMB F
  refine ⟨K, ?_⟩
  intro k r c Φ y γ m a i₀ hkr hγ hγ0 ha hm hram hord hminors hdet
  -- the good-level count
  have hcount : m ≤ a * K.eval (WilkiesDesign.E.atomDeg Φ) :=
    hK k r c Φ y γ m a i₀ hkr hγ hγ0 ha hm hram hord hminors hdet
  -- the minimal order of a partial derivative of `Φ` along the arc
  let ordOf : Fin k → ℕ∞ := fun l =>
    analyticOrderAt (fun t : ℝ => WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c l Φ) (γ t)) 0
  obtain ⟨i, -, hi⟩ :=
    Finset.exists_min_image (Finset.univ : Finset (Fin k)) ordOf ⟨i₀, Finset.mem_univ i₀⟩
  have hmin : ∀ l : Fin k, ordOf i ≤ ordOf l := fun l => hi l (Finset.mem_univ l)
  -- the gradient of `eaEval c Φ` is `eaEval c (eaD c · Φ)`
  have hgrad : ∀ l : Fin k,
      (fun t : ℝ => Work.WilE3.Taylor.grad (fun z : Fin k → ℝ => WilkiesDesign.E.eaEval c Φ z)
          (γ t) l)
        = fun t : ℝ => WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c l Φ) (γ t) := by
    intro l
    funext t
    exact Work.Taylor.Grad.grad_eaEval c Φ (γ t) l
  -- the minimal order is finite: otherwise the chain rule with the numerical bound `m + 1`
  -- contradicts `m` finite
  have hne_top : ordOf i ≠ ⊤ := by
    intro htop
    have hr : ∀ l : Fin k, ((m + 1 : ℕ) : ℕ∞) ≤
        analyticOrderAt (fun t : ℝ =>
          Work.WilE3.Taylor.grad (fun z : Fin k → ℝ => WilkiesDesign.E.eaEval c Φ z)
            (γ t) l) 0 := by
      intro l
      rw [hgrad l]
      have hle : ordOf l = ⊤ := le_antisymm le_top (by rw [← htop]; exact hmin l)
      show ((m + 1 : ℕ) : ℕ∞) ≤ ordOf l
      rw [hle]
      exact le_top
    have hbad := Work.WilE3.Taylor.Grad.gradOrderLe
      (Φ := fun z : Fin k → ℝ => WilkiesDesign.E.eaEval c Φ z)
      hγ (fun x => Work.WilE3.eaEval_analytic c Φ x) ha hm hram hord hr
    omega
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hne_top
  refine ⟨i, n, ?_, ?_⟩
  · -- `ord₀ (∂ᵢΦ ∘ γ) = n`
    show ordOf i = (n : ℕ∞)
    exact hn.symm
  · -- the order bound
    set D := K.eval (WilkiesDesign.E.atomDeg Φ) with hD
    -- the chain-rule bound `n + a ≤ m`
    have hr : ∀ l : Fin k, (n : ℕ∞) ≤
        analyticOrderAt (fun t : ℝ =>
          Work.WilE3.Taylor.grad (fun z : Fin k → ℝ => WilkiesDesign.E.eaEval c Φ z)
            (γ t) l) 0 := by
      intro l
      rw [hgrad l]
      show (n : ℕ∞) ≤ ordOf l
      rw [hn]
      exact hmin l
    have hnle : n + a ≤ m := Work.WilE3.Taylor.Grad.gradOrderLe
      (Φ := fun z : Fin k → ℝ => WilkiesDesign.E.eaEval c Φ z)
      hγ (fun x => Work.WilE3.eaEval_analytic c Φ x) ha hm hram hord hr
    -- arithmetic
    have ha_le_m : a ≤ m := by omega
    have hnm : n ≤ m - a := (Nat.le_sub_iff_add_le ha_le_m).mpr hnle
    have hkey : m ≤ (D + 1) * a := by
      calc m ≤ a * D := hcount
        _ ≤ a * (D + 1) := Nat.mul_le_mul_left a (Nat.le_succ D)
        _ = (D + 1) * a := Nat.mul_comm _ _
    calc (D + 1) * n ≤ (D + 1) * (m - a) := Nat.mul_le_mul_left _ hnm
      _ = (D + 1) * m - (D + 1) * a := Nat.mul_sub_left_distrib _ _ _
      _ ≤ (D + 1) * m - m := Nat.sub_le_sub_left hkey ((D + 1) * m)
      _ = D * m := by
          have h : (D + 1) * m = D * m + m := by ring
          rw [h, Nat.add_sub_cancel]

end Work.Taylor.Grad
