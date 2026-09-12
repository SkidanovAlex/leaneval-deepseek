import Mathlib
import Submission.LMWalk

/-!
Probability-space infrastructure for the Lovett--Meka walk.

The walk of `T` steps lives on `Omega n T := Fin T → Vec n` with the product of `T`
independent standard Gaussians.
-/

open scoped BigOperators RealInnerProductSpace
open MeasureTheory ProbabilityTheory

noncomputable section

namespace Submission.Discrepancy

abbrev Omega (n T : ℕ) := Fin T → Vec n

/-- The probability measure on `Omega n T`. -/
def mu (n T : ℕ) : Measure (Omega n T) := Measure.pi (fun _ : Fin T => stdGaussian (Vec n))

instance (n T : ℕ) : IsProbabilityMeasure (mu n T) := by
  unfold mu
  infer_instance

/-- The Gaussian input at step `s < T`, extended by zero outside. -/
def oracle (n T : ℕ) (ω : Omega n T) : ℕ → Vec n :=
  fun s => if h : s < T then ω ⟨s, h⟩ else 0

/-- The position after `t` steps. -/
def Xn {ι : Type*} [Fintype ι] (n T : ℕ) (δ γ : ℝ) (x0 : Vec n) (v : ι → Vec n) (c : ι → ℝ)
    (ω : Omega n T) (t : ℕ) : Vec n :=
  xseq δ γ x0 v c (oracle n T ω) t

/-- The frozen-variable set after `t` steps. -/
def AVn {ι : Type*} [Fintype ι] (n T : ℕ) (δ γ : ℝ) (x0 : Vec n) (v : ι → Vec n) (c : ι → ℝ)
    (ω : Omega n T) (t : ℕ) : Finset (Fin n) :=
  frozenVars δ (Xn n T δ γ x0 v c ω t)

/-- The frozen-row set after `t` steps. -/
def BVn {ι : Type*} [Fintype ι] (n T : ℕ) (δ γ : ℝ) (x0 : Vec n) (v : ι → Vec n) (c : ι → ℝ)
    (ω : Omega n T) (t : ℕ) : Finset ι :=
  frozenRows δ x0 v c (Xn n T δ γ x0 v c ω t)

/-- The projection of the Gaussian at step `t+1`. -/
def Proj {ι : Type*} [Fintype ι] (n T : ℕ) (δ γ : ℝ) (x0 : Vec n) (v : ι → Vec n) (c : ι → ℝ)
    (ω : Omega n T) (t : ℕ) : Vec n :=
  walkProj v (AVn n T δ γ x0 v c ω t) (BVn n T δ γ x0 v c ω t) (oracle n T ω t)

lemma Xn_succ {ι : Type*} [Fintype ι] (n T : ℕ) (δ γ : ℝ) (x0 : Vec n) (v : ι → Vec n)
    (c : ι → ℝ) (ω : Omega n T) (t : ℕ) (ht : t < T) :
    Xn n T δ γ x0 v c ω (t + 1) =
      Xn n T δ γ x0 v c ω t + γ • Proj n T δ γ x0 v c ω t := by
  rfl

lemma xseq_congr {n : ℕ} {ι : Type*} [Fintype ι] (δ γ : ℝ) (x0 : Vec n) (v : ι → Vec n)
    (c : ι → ℝ) {g g' : ℕ → Vec n} {t : ℕ} (h : ∀ s : ℕ, s < t → g s = g' s) :
    xseq δ γ x0 v c g t = xseq δ γ x0 v c g' t := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [xseq_succ, xseq_succ, ih (fun s hs => h s (Nat.lt_succ_of_lt hs))]
      congr 1
      have ihx := ih (fun s hs => h s (Nat.lt_succ_of_lt hs))
      unfold sinc
      rw [ihx, h t (Nat.lt_succ_self t)]

lemma Xn_telescope {ι : Type*} [Fintype ι] (n T : ℕ) (δ γ : ℝ) (x0 : Vec n) (v : ι → Vec n)
    (c : ι → ℝ) (ω : Omega n T) (t : ℕ) (ht : t ≤ T) :
    Xn n T δ γ x0 v c ω t - x0 = γ • ∑ s ∈ Finset.range t, Proj n T δ γ x0 v c ω s := by
  induction t with
  | zero => simp [Xn]
  | succ t ih =>
      have ht2 : t < T := Nat.lt_of_succ_le ht
      calc Xn n T δ γ x0 v c ω (t + 1) - x0
          = (Xn n T δ γ x0 v c ω t - x0) + γ • Proj n T δ γ x0 v c ω t := by
              rw [Xn_succ (n := n) (T := T) δ γ x0 v c ω t ht2]
              abel
      _ = γ • ∑ s ∈ Finset.range t, Proj n T δ γ x0 v c ω s + γ • Proj n T δ γ x0 v c ω t := by
              rw [ih (Nat.le_of_succ_le ht)]
      _ = γ • (∑ s ∈ Finset.range t, Proj n T δ γ x0 v c ω s + Proj n T δ γ x0 v c ω t) := by
              rw [smul_add]
      _ = γ • ∑ s ∈ Finset.range (t + 1), Proj n T δ γ x0 v c ω s := by
              rw [Finset.sum_range_succ]

/-- The last-coordinate peel as a measurable equivalence. -/
def peelEquiv (n T : ℕ) : Omega n (T + 1) ≃ᵐ (Vec n × Omega n T) :=
  MeasurableEquiv.piFinSuccAbove (fun _ : Fin (T + 1) => Vec n) (Fin.last T)

lemma peelEquiv_apply (n T : ℕ) (ω : Omega n (T+1)) :
    peelEquiv n T ω = (ω (Fin.last T), Fin.init ω) := by
  ext x <;> simp [peelEquiv, Fin.init_def]

lemma peelEquiv_symm_apply (n T : ℕ) (g : Vec n) (p : Omega n T) :
    (peelEquiv n T).symm (g, p) = Fin.snoc (α := fun _ : Fin (T + 1) => Vec n) p g := by
  simp [peelEquiv, Fin.insertNthEquiv]

lemma peel_measurePreserving (n T : ℕ) :
    (mu n (T + 1)).map (fun ω : Omega n (T+1) => (ω (Fin.last T), Fin.init ω))
      = (stdGaussian (Vec n)).prod (mu n T) := by
  unfold mu
  have hp := MeasureTheory.measurePreserving_piFinSuccAbove
    (μ := fun _ : Fin (T + 1) => stdGaussian (Vec n)) (Fin.last T)
  change (Measure.pi (fun _ : Fin (T+1) => stdGaussian (Vec n))).map
      (fun ω : Omega n (T+1) => (ω (Fin.last T), Fin.init ω))
    = (stdGaussian (Vec n)).prod (Measure.pi (fun _ : Fin T => stdGaussian (Vec n)))
  have hfn : (fun ω : Omega n (T+1) => peelEquiv n T ω) =
      (fun ω : Omega n (T+1) => (ω (Fin.last T), Fin.init ω)) := by
    funext ω
    exact peelEquiv_apply n T ω
  rw [← hfn]
  exact hp.map_eq

/-- Reusable peel identity (lintegral form): integrate out the last Gaussian. -/
lemma lintegral_snoc_form (n T : ℕ) (F : Vec n → Omega n T → ENNReal)
    (hmeas : Measurable (fun y : Vec n × Omega n T => F y.1 y.2)) :
    (∫⁻ ω : Omega n (T + 1), F (ω (Fin.last T)) (Fin.init ω) ∂(mu n (T + 1))) =
      ∫⁻ g : Vec n, ∫⁻ p : Omega n T, F g p ∂(mu n T) ∂(stdGaussian (Vec n)) := by
  have hmap : (mu n (T + 1)).map (fun ω : Omega n (T+1) => (ω (Fin.last T), Fin.init ω))
      = (stdGaussian (Vec n)).prod (mu n T) := peel_measurePreserving n T
  calc
    (∫⁻ ω : Omega n (T + 1), F (ω (Fin.last T)) (Fin.init ω) ∂(mu n (T + 1)))
      = ∫⁻ y : Vec n × Omega n T, F y.1 y.2
          ∂((mu n (T + 1)).map (fun ω : Omega n (T+1) => (ω (Fin.last T), Fin.init ω))) := by
          rw [MeasureTheory.lintegral_map hmeas (by fun_prop)]
    _ = ∫⁻ g : Vec n, ∫⁻ p : Omega n T, F g p ∂(mu n T) ∂(stdGaussian (Vec n)) := by
          rw [hmap]
          rw [MeasureTheory.lintegral_prod]
          exact hmeas.aemeasurable

/-- Keep only the first `t` coordinates. -/
def first {n : ℕ} (T t : ℕ) (ht : t ≤ T) (ω : Omega n T) : Omega n t :=
  fun s : Fin t => ω ⟨s.val, by omega⟩

lemma first_succ {n : ℕ} (T : ℕ) (ω : Omega n (T + 1)) (t : ℕ) (ht : t ≤ T) :
    first (T + 1) t (by omega) ω = first T t ht (Fin.init ω) := by
  ext s
  simp [first, Fin.init]

lemma first_id {n : ℕ} (T : ℕ) (ω : Omega n (T + 1)) :
    first (T + 1) (T + 1) (by omega) ω = ω := by
  ext s
  simp [first]

/-- Expectation of a function of the first `t` coordinates only depends on the first `t` Gaussians. -/
lemma lintegral_first (n T t : ℕ) (ht : t ≤ T) (F : Omega n t → ENNReal)
    (hmeas : Measurable F) :
    (∫⁻ ω : Omega n T, F (first T t ht ω) ∂(mu n T)) = ∫⁻ ω : Omega n t, F ω ∂(mu n t) := by
  induction T with
  | zero =>
      have hz : t = 0 := Nat.eq_zero_of_le_zero ht
      subst t
      apply lintegral_congr_ae
      filter_upwards with ω
      congr 1
  | succ T ih =>
      by_cases htT : t ≤ T
      · calc
          (∫⁻ ω : Omega n (T + 1), F (first (T+1) t (by omega) ω) ∂(mu n (T+1)))
            = ∫⁻ ω : Omega n (T + 1), F (first T t htT (Fin.init ω)) ∂(mu n (T+1)) := by
                rw [show (fun ω : Omega n (T + 1) => F (first (T+1) t (by omega) ω)) =
                      fun ω : Omega n (T + 1) => F (first T t htT (Fin.init ω)) by
                  funext ω
                  congr 1]
          _ = ∫⁻ g : Vec n, ∫⁻ p : Omega n T, F (first T t htT p) ∂(mu n T)
                ∂(stdGaussian (Vec n)) := by
                let F'' : Vec n → Omega n T → ENNReal := fun g p => F (first T t htT p)
                have hm1 : Measurable (fun y : Vec n × Omega n T => first T t htT y.2) := by
                  rw [measurable_pi_iff]
                  intro i
                  exact (measurable_pi_apply (⟨i.val, by omega⟩ : Fin T)).comp measurable_snd
                have hmeas'' : Measurable (fun y : Vec n × Omega n T => F'' y.1 y.2) := by
                  dsimp [F'']
                  exact hmeas.comp hm1
                rw [← lintegral_snoc_form n T F'' hmeas'']
          _ = ∫⁻ p : Omega n T, F (first T t htT p) ∂(mu n T) := by
                rw [lintegral_const]
                simp
          _ = ∫⁻ p : Omega n t, F p ∂(mu n t) := ih htT
      · have htt : t = T + 1 := by omega
        subst t
        apply lintegral_congr_ae
        filter_upwards with ω
        congr 1

/-- The appended prefix steps equal the prefix walk. -/
lemma Xn_snoc {ι : Type*} [Fintype ι] (n T : ℕ) (δ γ : ℝ) (x0 : Vec n) (v : ι → Vec n)
    (c : ι → ℝ) (g : Vec n) (p : Omega n T) (t : ℕ) (ht : t ≤ T) :
    Xn n (T+1) δ γ x0 v c (Fin.snoc (α := fun _ : Fin (T + 1) => Vec n) p g) t =
      Xn n T δ γ x0 v c p t := by
  unfold Xn
  apply xseq_congr δ γ x0 v c
  intro s hs
  have hsT : s < T := by omega
  have hs1 : s < T + 1 := by omega
  ext i
  simp [oracle, hsT, hs1]
  have hfin : ((⟨s, hsT⟩ : Fin T).castSucc : Fin (T + 1)) = ⟨s, hs1⟩ := by
    apply Fin.ext
    rfl
  rw [← hfin]
  rw [Fin.snoc_castSucc]

/-- The last step of the appended walk. -/
lemma last_step {n : ℕ} {ι : Type*} [Fintype ι] (T' : ℕ) (δ γ : ℝ) (x0 : Vec n) (v : ι → Vec n)
    (c : ι → ℝ) (g : Vec n) (p : Omega n T') :
    Xn n (T'+1) δ γ x0 v c (Fin.snoc (α := fun _ : Fin (T' + 1) => Vec n) p g) (T' + 1) =
      Xn n T' δ γ x0 v c p T' + γ • walkProj v
        (frozenVars δ (Xn n T' δ γ x0 v c p T'))
        (frozenRows δ x0 v c (Xn n T' δ γ x0 v c p T')) g := by
  rw [Xn_succ (n := n) (T := T'+1) δ γ x0 v c
    (Fin.snoc (α := fun _ : Fin (T' + 1) => Vec n) p g) T' (Nat.lt_succ_self T')]
  have hX := Xn_snoc (n := n) (T := T') δ γ x0 v c g p T' (le_refl T')
  rw [hX]
  congr 1
  have hg : oracle n (T'+1) (Fin.snoc (α := fun _ : Fin (T'+1) => Vec n) p g) T' = g := by
    unfold oracle
    rw [dif_pos (Nat.lt_succ_self T')]
    congr 1
    have hlast : (⟨T', Nat.lt_succ_self T'⟩ : Fin (T'+1)) = Fin.last T' := by
      apply Fin.ext
      simp [Fin.last]
    rw [hlast]
    rw [Fin.snoc_last]
  unfold Proj AVn BVn
  rw [hX]
  rw [hg]

/-- The appended walk from a point: value equals sum. -/
lemma Xn_app_value {n : ℕ} {ι : Type*} [Fintype ι] (T' : ℕ) (δ γ : ℝ) (x0 : Vec n)
    (v : ι → Vec n) (c : ι → ℝ) (g : Vec n) (p : Omega n T') (w : Vec n) :
    vin (Xn n (T'+1) δ γ x0 v c (Fin.snoc (α := fun _ : Fin (T' + 1) => Vec n) p g) (T' + 1) - x0) w
      = vin (Xn n T' δ γ x0 v c p T' - x0) w
        + γ * vin (walkProj v (frozenVars δ (Xn n T' δ γ x0 v c p T'))
            (frozenRows δ x0 v c (Xn n T' δ γ x0 v c p T')) g) w := by
  rw [last_step (n := n) (T' := T') δ γ x0 v c g p]
  have hlin : vin (Xn n T' δ γ x0 v c p T' + γ • walkProj v
        (frozenVars δ (Xn n T' δ γ x0 v c p T')) (frozenRows δ x0 v c (Xn n T' δ γ x0 v c p T')) g - x0) w
      = vin (Xn n T' δ γ x0 v c p T' - x0) w
        + γ * vin (walkProj v (frozenVars δ (Xn n T' δ γ x0 v c p T'))
            (frozenRows δ x0 v c (Xn n T' δ γ x0 v c p T')) g) w := by
    have hv : Xn n T' δ γ x0 v c p T' + γ • walkProj v
          (frozenVars δ (Xn n T' δ γ x0 v c p T')) (frozenRows δ x0 v c (Xn n T' δ γ x0 v c p T')) g - x0
        = (Xn n T' δ γ x0 v c p T' - x0) + γ • walkProj v
          (frozenVars δ (Xn n T' δ γ x0 v c p T')) (frozenRows δ x0 v c (Xn n T' δ γ x0 v c p T')) g := by
        abel
    rw [hv]
    simp [vin, inner_add_left, inner_smul_left]
  exact hlin


end Discrepancy

end Submission
