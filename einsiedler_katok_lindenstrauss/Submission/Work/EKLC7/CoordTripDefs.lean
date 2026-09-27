import Mathlib
import Submission.Work.EKLC7.Defs
import Submission.Work.EKLC7.HeisMul
import Submission.Work.EKLC7.HeisShift
import Submission.Work.EKLC7.HeisFactor
import Submission.Work.EKLC7.CoordTest
import Submission.Work.EKLC7.SupportFacts

/-!
# C7 (`CoordTrip`): the coordinate bookkeeping of the two Heisenberg parametrisations

This file collects the definitions and elementary lemmas used by `Work.EKLC7.CoordTrip`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.EKLC7

open MeasureTheory Filter Topology
open Work.EKLContract
open Work.EKLContract.Lemmas

/-- The coordinate map `g ↦ (g_ij, g_ik, g_jk)`. -/
def coordMap (i j k : Fin 3) : SL3 → ℝ × ℝ × ℝ :=
  fun g => (pcoord i j g, qcoord i k g, rcoord j k g)

/-- The product of a triple of elements of `SL₃(ℝ)`. -/
def mult3 : SL3 × SL3 × SL3 → SL3 := fun u => u.1 * u.2.1 * u.2.2

/-- The Heisenberg element whose product decomposition is `u_ij(x.1) * u_jk(x.2.1) * u_ik(x.2.2)`. -/
def heisA {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (x : ℝ × ℝ × ℝ) : SL3 :=
  heis hij hjk hik x.1 (x.1 * x.2.1 + x.2.2) x.2.1

/-- The Heisenberg element whose product decomposition is `u_jk(x.2.1) * u_ij(x.1) * u_ik(x.2.2)`. -/
def heisB {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (x : ℝ × ℝ × ℝ) : SL3 :=
  heis hij hjk hik x.2.1 x.2.2 x.1

/-- The triple `(u_ij(x.1), u_jk(x.2.1), u_ik(x.2.2))`. -/
def paramA {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (x : ℝ × ℝ × ℝ) :
    SL3 × SL3 × SL3 :=
  (uij hij x.1, uij hjk x.2.1, uij hik x.2.2)

/-- The triple `(u_jk(x.1), u_ij(x.2.1), u_ik(x.2.2))`. -/
def paramB {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (x : ℝ × ℝ × ℝ) :
    SL3 × SL3 × SL3 :=
  (uij hjk x.1, uij hij x.2.1, uij hik x.2.2)

/-- The coordinates of `heisA x`: `(x.1, x.1 * x.2.1 + x.2.2, x.2.1)`. -/
def shearA : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ := fun x => (x.1, x.1 * x.2.1 + x.2.2, x.2.1)

/-- The coordinates of `heisB x`: `(x.1, x.2.2, x.2.1)`. -/
def shearB : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ := fun x => (x.2.1, x.2.2, x.1)

theorem continuous_toMat_entry (a b : Fin 3) : Continuous (fun g : SL3 => toMat g a b) :=
  (continuous_entry a b).comp continuous_subtype_val

/-- `paramA` as a `Prod.map`. -/
theorem paramA_eq {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    paramA hij hjk hik = Prod.map (uij hij) (Prod.map (uij hjk) (uij hik)) := rfl

/-- `paramB` as a `Prod.map`. -/
theorem paramB_eq {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    paramB hij hjk hik = Prod.map (uij hjk) (Prod.map (uij hij) (uij hik)) := rfl

/-! ## Coordinates of the root groups -/

/-- On `U_ij` the `(i,j)`-entry is the parameter. -/
theorem uij_of_mem_pcoord {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    {g : SL3} (hg : g ∈ Uij hij) : uij hij (pcoord i j g) = g := by
  obtain ⟨s, rfl⟩ := (horoUij_mem_iff hij g).mp hg
  have hs : pcoord i j (uij hij s) = s := by
    rw [← heis_uij hij hjk hik s]
    exact pcoord_heis hij hjk hik s 0 0
  rw [hs]

/-- On `U_jk` the `(j,k)`-entry is the parameter. -/
theorem uij_of_mem_rcoord {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    {g : SL3} (hg : g ∈ Uij hjk) : uij hjk (rcoord j k g) = g := by
  obtain ⟨s, rfl⟩ := (horoUij_mem_iff hjk g).mp hg
  have hs : rcoord j k (uij hjk s) = s := by
    rw [← heis_ujk hij hjk hik s]
    exact rcoord_heis hij hjk hik 0 0 s
  rw [hs]

/-- On `U_ik` the `(i,k)`-entry is the parameter. -/
theorem uij_of_mem_qcoord {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    {g : SL3} (hg : g ∈ Uij hik) : uij hik (qcoord i k g) = g := by
  obtain ⟨s, rfl⟩ := (horoUij_mem_iff hik g).mp hg
  have hs : qcoord i k (uij hik s) = s := by
    rw [← heis_uik hij hjk hik s]
    exact qcoord_heis hij hjk hik 0 s 0
  rw [hs]

/-! ## Coordinates of products -/

/-- The coordinates of `g₁ * g₂ * g₃` for `g₁ ∈ U_ij`, `g₂ ∈ U_jk`, `g₃ ∈ U_ik`. -/
theorem coordMap_mul {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    {g₁ g₂ g₃ : SL3} (h₁ : g₁ ∈ Uij hij) (h₂ : g₂ ∈ Uij hjk) (h₃ : g₃ ∈ Uij hik) :
    coordMap i j k (g₁ * g₂ * g₃)
      = (pcoord i j g₁, pcoord i j g₁ * rcoord j k g₂ + qcoord i k g₃, rcoord j k g₂) := by
  obtain ⟨p, rfl⟩ := (horoUij_mem_iff hij g₁).mp h₁
  obtain ⟨r, rfl⟩ := (horoUij_mem_iff hjk g₂).mp h₂
  obtain ⟨q, rfl⟩ := (horoUij_mem_iff hik g₃).mp h₃
  have hp : pcoord i j (uij hij p) = p := by
    rw [← heis_uij hij hjk hik p]; exact pcoord_heis hij hjk hik p 0 0
  have hr : rcoord j k (uij hjk r) = r := by
    rw [← heis_ujk hij hjk hik r]; exact rcoord_heis hij hjk hik 0 0 r
  have hq : qcoord i k (uij hik q) = q := by
    rw [← heis_uik hij hjk hik q]; exact qcoord_heis hij hjk hik 0 q 0
  rw [coordMap, hp, hr, hq, ← heis_uij hij hjk hik p, ← heis_ujk hij hjk hik r,
    ← heis_uik hij hjk hik q, heis_mul, heis_mul,
    pcoord_heis hij hjk hik, qcoord_heis hij hjk hik, rcoord_heis hij hjk hik]
  refine Prod.ext ?_ ?_
  · ring
  · refine Prod.ext ?_ ?_ <;> ring

/-- The coordinates of `g₁ * g₂ * g₃` for `g₁ ∈ U_jk`, `g₂ ∈ U_ij`, `g₃ ∈ U_ik`. -/
theorem coordMap_mulB {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    {g₁ g₂ g₃ : SL3} (h₁ : g₁ ∈ Uij hjk) (h₂ : g₂ ∈ Uij hij) (h₃ : g₃ ∈ Uij hik) :
    coordMap i j k (g₁ * g₂ * g₃)
      = (pcoord i j g₂, qcoord i k g₃, rcoord j k g₁) := by
  obtain ⟨r, rfl⟩ := (horoUij_mem_iff hjk g₁).mp h₁
  obtain ⟨p, rfl⟩ := (horoUij_mem_iff hij g₂).mp h₂
  obtain ⟨q, rfl⟩ := (horoUij_mem_iff hik g₃).mp h₃
  have hp : pcoord i j (uij hij p) = p := by
    rw [← heis_uij hij hjk hik p]; exact pcoord_heis hij hjk hik p 0 0
  have hr : rcoord j k (uij hjk r) = r := by
    rw [← heis_ujk hij hjk hik r]; exact rcoord_heis hij hjk hik 0 0 r
  have hq : qcoord i k (uij hik q) = q := by
    rw [← heis_uik hij hjk hik q]; exact qcoord_heis hij hjk hik 0 q 0
  rw [coordMap, hp, hr, hq, ← heis_ujk hij hjk hik r, ← heis_uij hij hjk hik p,
    ← heis_uik hij hjk hik q, heis_mul, heis_mul,
    pcoord_heis hij hjk hik, qcoord_heis hij hjk hik, rcoord_heis hij hjk hik]
  refine Prod.ext ?_ ?_
  · ring
  · refine Prod.ext ?_ ?_ <;> ring

/-! ## The parametrisation maps -/

/-- `mult3 ∘ paramA = heisA`. -/
theorem mult3_paramA {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (x : ℝ × ℝ × ℝ) : mult3 (paramA hij hjk hik x) = heisA hij hjk hik x := by
  rw [paramA, mult3, heisA, ← heis_uij hij hjk hik x.1, ← heis_ujk hij hjk hik x.2.1,
    ← heis_uik hij hjk hik x.2.2, heis_mul, heis_mul]
  exact heis_congr hij hjk hik (by ring) (by ring) (by ring)

/-- `mult3 ∘ paramB = heisB`. -/
theorem mult3_paramB {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (x : ℝ × ℝ × ℝ) : mult3 (paramB hij hjk hik x) = heisB hij hjk hik x := by
  rw [paramB, mult3, heisB, ← heis_ujk hij hjk hik x.1, ← heis_uij hij hjk hik x.2.1,
    ← heis_uik hij hjk hik x.2.2, heis_mul, heis_mul]
  exact heis_congr hij hjk hik (by ring) (by ring) (by ring)

/-- `coordMap ∘ heisA = shearA`. -/
theorem coordMap_heisA {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (x : ℝ × ℝ × ℝ) : coordMap i j k (heisA hij hjk hik x) = shearA x := by
  rw [heisA, coordMap, shearA, pcoord_heis hij hjk hik, qcoord_heis hij hjk hik,
    rcoord_heis hij hjk hik]

/-- `coordMap ∘ heisB = shearB`. -/
theorem coordMap_heisB {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (x : ℝ × ℝ × ℝ) : coordMap i j k (heisB hij hjk hik x) = shearB x := by
  rw [heisB, coordMap, shearB, pcoord_heis hij hjk hik, qcoord_heis hij hjk hik,
    rcoord_heis hij hjk hik]

/-! ## Entry bounds on the parametrisations -/

theorem pcoord_heisA {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (x : ℝ × ℝ × ℝ) : toMat (heisA hij hjk hik x) i j = x.1 :=
  pcoord_heis hij hjk hik x.1 (x.1 * x.2.1 + x.2.2) x.2.1

theorem rcoord_heisA {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (x : ℝ × ℝ × ℝ) : toMat (heisA hij hjk hik x) j k = x.2.1 :=
  rcoord_heis hij hjk hik x.1 (x.1 * x.2.1 + x.2.2) x.2.1

theorem qcoord_heisA {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (x : ℝ × ℝ × ℝ) : toMat (heisA hij hjk hik x) i k = x.1 * x.2.1 + x.2.2 :=
  qcoord_heis hij hjk hik x.1 (x.1 * x.2.1 + x.2.2) x.2.1

theorem pcoord_heisB {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (x : ℝ × ℝ × ℝ) : toMat (heisB hij hjk hik x) i j = x.2.1 :=
  pcoord_heis hij hjk hik x.2.1 x.2.2 x.1

theorem rcoord_heisB {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (x : ℝ × ℝ × ℝ) : toMat (heisB hij hjk hik x) j k = x.1 :=
  rcoord_heis hij hjk hik x.2.1 x.2.2 x.1

theorem qcoord_heisB {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (x : ℝ × ℝ × ℝ) : toMat (heisB hij hjk hik x) i k = x.2.2 :=
  qcoord_heis hij hjk hik x.2.1 x.2.2 x.1

/-- The entries of `heisA x` bound `x`. -/
theorem abs_le_of_abs_heisA {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    {M : ℝ} {x : ℝ × ℝ × ℝ}
    (h : ∀ a b : Fin 3, |toMat (heisA hij hjk hik x) a b| ≤ M) :
    |x.1| ≤ M ∧ |x.2.1| ≤ M ∧ |x.2.2| ≤ M + M ^ 2 := by
  have h1 : |x.1| ≤ M := by rw [← pcoord_heisA hij hjk hik x]; exact h i j
  have h3 : |x.2.1| ≤ M := by rw [← rcoord_heisA hij hjk hik x]; exact h j k
  have h2 : |x.1 * x.2.1 + x.2.2| ≤ M := by rw [← qcoord_heisA hij hjk hik x]; exact h i k
  refine ⟨h1, h3, ?_⟩
  have h4 : |x.2.2| ≤ |x.1 * x.2.1 + x.2.2| + |x.1 * x.2.1| := by
    have habs : |x.2.2| = |(x.1 * x.2.1 + x.2.2) - x.1 * x.2.1| := by congr 1; ring
    rw [habs]
    calc |(x.1 * x.2.1 + x.2.2) - x.1 * x.2.1|
        = |(x.1 * x.2.1 + x.2.2) + (-(x.1 * x.2.1))| := by rw [sub_eq_add_neg]
      _ ≤ |x.1 * x.2.1 + x.2.2| + |-(x.1 * x.2.1)| := abs_add_le _ _
      _ = |x.1 * x.2.1 + x.2.2| + |x.1 * x.2.1| := by rw [abs_neg]
  have h5 : |x.1 * x.2.1| ≤ M * M := by
    rw [abs_mul]
    exact mul_le_mul h1 h3 (abs_nonneg _) (le_trans (abs_nonneg _) h1)
  calc |x.2.2| ≤ M + M * M := by linarith
    _ = M + M ^ 2 := by ring

/-- The last coordinate is bounded in terms of the other two. -/
theorem abs_bound_last {M : ℝ} {x : ℝ × ℝ × ℝ} (h1 : |x.1| ≤ M)
    (h2 : |x.1 * x.2.1 + x.2.2| ≤ M) (h3 : |x.2.1| ≤ M) : |x.2.2| ≤ M + M ^ 2 := by
  have habs : |x.2.2| = |(x.1 * x.2.1 + x.2.2) - x.1 * x.2.1| := by congr 1; ring
  rw [habs]
  calc |(x.1 * x.2.1 + x.2.2) - x.1 * x.2.1|
      ≤ |x.1 * x.2.1 + x.2.2| + |x.1 * x.2.1| := by
        rw [sub_eq_add_neg]
        calc |(x.1 * x.2.1 + x.2.2) + -(x.1 * x.2.1)|
            ≤ |x.1 * x.2.1 + x.2.2| + |-(x.1 * x.2.1)| := abs_add_le _ _
          _ = |x.1 * x.2.1 + x.2.2| + |x.1 * x.2.1| := by rw [abs_neg]
    _ ≤ M + M * M := by
        have h4 : |x.1 * x.2.1| ≤ M * M := by
          rw [abs_mul]
          exact mul_le_mul h1 h3 (abs_nonneg _) (le_trans (abs_nonneg _) h1)
        linarith
    _ = M + M ^ 2 := by ring

/-- The entries of `heisB x` bound `x`. -/
theorem abs_le_of_abs_heisB {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    {M : ℝ} {x : ℝ × ℝ × ℝ}
    (h : ∀ a b : Fin 3, |toMat (heisB hij hjk hik x) a b| ≤ M) :
    |x.1| ≤ M ∧ |x.2.1| ≤ M ∧ |x.2.2| ≤ M := by
  exact ⟨by rw [← rcoord_heisB hij hjk hik x]; exact h j k,
         by rw [← pcoord_heisB hij hjk hik x]; exact h i j,
         by rw [← qcoord_heisB hij hjk hik x]; exact h i k⟩

/-! ## Continuity of the parametrisations -/

theorem continuous_mult3 : Continuous mult3 := by
  show Continuous (fun u : SL3 × SL3 × SL3 => u.1 * u.2.1 * u.2.2)
  exact (continuous_fst.mul continuous_snd.fst).mul continuous_snd.snd

theorem continuous_paramA {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    Continuous (paramA hij hjk hik) := by
  rw [paramA_eq hij hjk hik]
  exact Continuous.prodMap (horoUij_cont hij)
    (Continuous.prodMap (horoUij_cont hjk) (horoUij_cont hik))

theorem continuous_paramB {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    Continuous (paramB hij hjk hik) := by
  rw [paramB_eq hij hjk hik]
  exact Continuous.prodMap (horoUij_cont hjk)
    (Continuous.prodMap (horoUij_cont hij) (horoUij_cont hik))

theorem continuous_heisA {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    Continuous (heisA hij hjk hik) := by
  show Continuous (fun x : ℝ × ℝ × ℝ => heis hij hjk hik x.1 (x.1 * x.2.1 + x.2.2) x.2.1)
  simp only [heis]
  have hc : Continuous (fun x : ℝ × ℝ × ℝ => x.1 * x.2.1 + x.2.2 - x.1 * x.2.1) := by fun_prop
  have h1 : Continuous (fun x : ℝ × ℝ × ℝ => uij hij x.1) :=
    (horoUij_cont hij).comp continuous_fst
  have h2 : Continuous (fun x : ℝ × ℝ × ℝ => uij hjk x.2.1) :=
    (horoUij_cont hjk).comp continuous_snd.fst
  have h3 : Continuous (fun x : ℝ × ℝ × ℝ => uij hik (x.1 * x.2.1 + x.2.2 - x.1 * x.2.1)) :=
    (horoUij_cont hik).comp hc
  exact (h1.mul h2).mul h3

theorem continuous_heisB {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    Continuous (heisB hij hjk hik) := by
  show Continuous (fun x : ℝ × ℝ × ℝ => heis hij hjk hik x.2.1 x.2.2 x.1)
  simp only [heis]
  have hc : Continuous (fun x : ℝ × ℝ × ℝ => x.2.2 - x.2.1 * x.1) := by fun_prop
  have h1 : Continuous (fun x : ℝ × ℝ × ℝ => uij hij x.2.1) :=
    (horoUij_cont hij).comp continuous_snd.fst
  have h2 : Continuous (fun x : ℝ × ℝ × ℝ => uij hjk x.1) :=
    (horoUij_cont hjk).comp continuous_fst
  have h3 : Continuous (fun x : ℝ × ℝ × ℝ => uij hik (x.2.2 - x.2.1 * x.1)) :=
    (horoUij_cont hik).comp hc
  exact (h1.mul h2).mul h3

theorem continuous_coordMap (i j k : Fin 3) : Continuous (coordMap i j k) := by
  show Continuous (fun g : SL3 => (pcoord i j g, qcoord i k g, rcoord j k g))
  exact (continuous_pcoord i j).prodMk ((continuous_qcoord i k).prodMk (continuous_rcoord j k))

theorem continuous_shearA : Continuous shearA := by
  show Continuous (fun x : ℝ × ℝ × ℝ => (x.1, x.1 * x.2.1 + x.2.2, x.2.1)); fun_prop

theorem continuous_shearB : Continuous shearB := by
  show Continuous (fun x : ℝ × ℝ × ℝ => (x.2.1, x.2.2, x.1)); fun_prop

/-! ## The defining products of the parametrisations -/

theorem prod_heisA {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (x : ℝ × ℝ × ℝ) :
    uij hij x.1 * uij hjk x.2.1 * uij hik x.2.2 = heisA hij hjk hik x := by
  rw [heisA, ← heis_uij hij hjk hik x.1, ← heis_ujk hij hjk hik x.2.1,
    ← heis_uik hij hjk hik x.2.2, heis_mul, heis_mul]
  exact heis_congr hij hjk hik (by ring) (by ring) (by ring)

theorem prod_heisB {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (x : ℝ × ℝ × ℝ) :
    uij hjk x.1 * uij hij x.2.1 * uij hik x.2.2 = heisB hij hjk hik x := by
  rw [heisB, ← heis_ujk hij hjk hik x.1, ← heis_uij hij hjk hik x.2.1,
    ← heis_uik hij hjk hik x.2.2, heis_mul, heis_mul]
  exact heis_congr hij hjk hik (by ring) (by ring) (by ring)

/-- The properness bound for `heisA`. -/
theorem heisA_lex {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    ∀ M : ℝ, ∃ M2 : ℝ, ∀ x : ℝ × ℝ × ℝ,
      (∀ a b : Fin 3, |toMat (heisA hij hjk hik x) a b| ≤ M) →
        |x.1| ≤ M2 ∧ |x.2.1| ≤ M2 ∧ |x.2.2| ≤ M2 := by
  intro M
  refine ⟨M + M ^ 2, fun x hx => ?_⟩
  obtain ⟨h1, h3, h2⟩ := abs_le_of_abs_heisA hij hjk hik hx
  have hM : M ≤ M + M ^ 2 := by nlinarith [sq_nonneg M]
  exact ⟨le_trans h1 hM, le_trans h3 hM, h2⟩

/-- The properness bound for `heisB`. -/
theorem heisB_lex {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    ∀ M : ℝ, ∃ M2 : ℝ, ∀ x : ℝ × ℝ × ℝ,
      (∀ a b : Fin 3, |toMat (heisB hij hjk hik x) a b| ≤ M) →
        |x.1| ≤ M2 ∧ |x.2.1| ≤ M2 ∧ |x.2.2| ≤ M2 := by
  intro M
  refine ⟨M, fun x hx => ?_⟩
  exact abs_le_of_abs_heisB hij hjk hik hx

end Work.EKLC7
