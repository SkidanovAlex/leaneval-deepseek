import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import ChallengeDeps
import Submission.DiagLimits
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
Grand canonical layer — the truncated grand-canonical ground-state energy.

For a cut-off density `ρmax ≥ 0` (so that all particle numbers below it are
admissible in a box of side `L`), and a chemical potential `μ ≥ 0`, define

    gcSet v μ ρmax L := { E(N,L) − μN | N : ℕ, N ≤ ρmax·L³ }
    gcBox v μ ρmax L := sInf (gcSet v μ ρmax L)

the grand-canonical ground-state "free energy" of a box of side `L`.  This
module proves the elementary facts that make the thermodynamic limit of
`gcBox/L³` (the pressure `p(μ)`) accessible:

- nonemptiness of `gcSet` (`N = 0` is admissible for `0 ≤ ρmax`, `0 ≤ L`);
- boundedness below of `gcSet` by `−μρmaxL³` (from `E ≥ 0`, `0 ≤ μ`);
- the value bounds relating `gcBox` to the energies of admissible states;
- volume-subadditivity over the grid: `gcBox(μ,ρmax,G_m) ≤ m³·gcBox(μ,ρmax,ℓ)`
  (`G_m := mℓ+(m−1)R`, from `boxEnergy_grid_balanced`);
- monotonicity in the side length: `gcBox(·,L)` is non-increasing in `L`.

Together these give, by the same window machinery as the canonical upper
side, the existence of the pressure `p(μ) := lim_L gcBox(μ,ρmax,L)/L³`; the
convexity of `p` in `μ` is then automatic (infimum of affine functions).
-/

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false

namespace BoseGases

open Filter Metric MeasureTheory
open scoped ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Admissible particle number in a box of side `L` under cut-off density `ρmax`:
`N ≤ ρmax·L³`. -/
def gcAdmissible (ρmax : ℝ) (L : ℝ) (N : ℕ) : Prop :=
  (N : ℝ) ≤ ρmax * L ^ 3

/-- The set of grand-canonical energy values (with chemical potential `μ`) over
admissible particle numbers. -/
def gcSet (v : ℝ³ → ℝ) (μ ρmax : ℝ) (L : ℝ) : Set ℝ :=
  {y : ℝ | ∃ N : ℕ, gcAdmissible ρmax L N ∧ y = boxEnergy N L v - μ * (N : ℝ)}

/-- The truncated grand-canonical ground-state energy of a box of side `L`. -/
noncomputable def gcBox (v : ℝ³ → ℝ) (μ ρmax : ℝ) (L : ℝ) : ℝ :=
  sInf (gcSet v μ ρmax L)

/-! ## Generic comparison of infima over sets of reals -/

/-- `sInf B ≤ sInf A` when every element of `A` is bounded below by an element
of `B`. -/
lemma sInf_le_sInf_of_le {A B : Set ℝ} (hA : A.Nonempty) (hB : BddBelow B)
    (h : ∀ a ∈ A, ∃ b ∈ B, b ≤ a) : sInf B ≤ sInf A := by
  apply le_csInf hA
  intro a ha
  rcases h a ha with ⟨b, hb, hba⟩
  exact le_trans (csInf_le hB hb) hba

/-! ## Nonemptiness and boundedness of `gcSet` -/

/-- `N = 0` is admissible for `0 ≤ ρmax`, `0 ≤ L`; hence `gcSet` is nonempty. -/
lemma gcSet_nonempty {v : ℝ³ → ℝ} {μ ρmax L : ℝ} (hρmax : 0 ≤ ρmax) (hL : 0 ≤ L) :
    (gcSet v μ ρmax L).Nonempty := by
  let y : ℝ := boxEnergy 0 L v - μ * (0 : ℝ)
  refine ⟨y, 0, ?_, ?_⟩
  · dsimp [gcAdmissible, y]
    simpa using mul_nonneg hρmax (pow_nonneg hL 3)
  · dsimp [y]
    simp

/-- `gcSet` is bounded below by `−μρmaxL³` (for `0 ≤ μ`, `0 ≤ v`, `0 < L`). -/
lemma gcSet_bddBelow {v : ℝ³ → ℝ} {μ ρmax L : ℝ} (hμ : 0 ≤ μ) (hρmax : 0 ≤ ρmax)
    (hL : 0 < L) (hv : 0 ≤ v) : BddBelow (gcSet v μ ρmax L) := by
  refine ⟨-μ * (ρmax * L ^ 3), ?_⟩
  intro y hy
  rcases hy with ⟨N, hNad, rfl⟩
  have hE : 0 ≤ boxEnergy N L v := boxEnergy_nonneg hL hv
  have hmul : μ * (N : ℝ) ≤ μ * (ρmax * L ^ 3) := by
    dsimp [gcAdmissible] at hNad
    exact mul_le_mul_of_nonneg_left hNad hμ
  nlinarith

/-- Every admissible state bounds `gcBox` from above. -/
lemma gcBox_le_value {v : ℝ³ → ℝ} {μ ρmax L : ℝ} (hμ : 0 ≤ μ) (hρmax : 0 ≤ ρmax)
    (hL : 0 < L) (hv : 0 ≤ v) {N : ℕ} (hNad : gcAdmissible ρmax L N) :
    gcBox v μ ρmax L ≤ boxEnergy N L v - μ * (N : ℝ) := by
  unfold gcBox
  apply csInf_le (gcSet_bddBelow (μ := μ) (ρmax := ρmax) (L := L) hμ hρmax hL hv)
  exact ⟨N, hNad, rfl⟩

/-- If a real `a` is `≤` every grand-canonical value then `a ≤ gcBox`. -/
lemma le_gcBox_of_forall {v : ℝ³ → ℝ} {μ ρmax L : ℝ} {a : ℝ} (hρmax : 0 ≤ ρmax)
    (hL : 0 ≤ L) (h : ∀ y, y ∈ gcSet v μ ρmax L → a ≤ y) : a ≤ gcBox v μ ρmax L := by
  unfold gcBox
  apply le_csInf (gcSet_nonempty (μ := μ) hρmax hL)
  exact h

/-! ## Volume subadditivity over the grid -/

/-- Grid subadditivity of the truncated grand-canonical energy: a box of side
`G_m := mℓ+(m−1)R` costs no more than `m³` copies of the `ℓ`-box. -/
lemma gcBox_grid_subadd {v : ℝ³ → ℝ} {μ ρmax ℓ R : ℝ} (hμ : 0 ≤ μ) (hρmax : 0 ≤ ρmax)
    (hℓ : 0 < ℓ) (hR : 0 ≤ R) (hv : 0 ≤ v) (hv1 : MemLp v 1)
    (hsupp : tsupport v ⊆ ball (0 : ℝ³) R) {m : ℕ} (hm : 1 ≤ m) :
    gcBox v μ ρmax (gridSide m ℓ R) ≤ (m : ℝ) ^ 3 * gcBox v μ ρmax ℓ := by
  let G := gridSide m ℓ R
  have hGpos : 0 < G := gridSide_pos hm hℓ hR
  have hLbox : (m : ℝ) * ℓ + ((m : ℝ) - 1) * R ≤ G := by rfl
  have hcore : ∀ y, y ∈ gcSet v μ ρmax ℓ →
      gcBox v μ ρmax G ≤ (m : ℝ) ^ 3 * y := by
    intro y hy
    rcases hy with ⟨n, hn, rfl⟩
    let N : ℕ := m ^ 3 * n
    have hcast : ((m ^ 3 * n : ℕ) : ℝ) = (m : ℝ) ^ 3 * (n : ℝ) := by
      rw [Nat.cast_mul, Nat.cast_pow]
    have hNad : gcAdmissible ρmax G N := by
      dsimp [gcAdmissible, N, G]
      rw [hcast]
      have hn' : (n : ℝ) ≤ ρmax * ℓ ^ 3 := by
        dsimp [gcAdmissible] at hn
        exact hn
      have hG3 : (m : ℝ) ^ 3 * ℓ ^ 3 ≤ G ^ 3 := by
        have hpart : 0 ≤ ((m : ℝ) - 1) * R := by
          have hmr : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
          exact mul_nonneg (by linarith) hR
        have hmℓ : (m : ℝ) * ℓ ≤ G := by
          dsimp [G]
          unfold gridSide
          nlinarith
        have hmℓ0 : 0 ≤ (m : ℝ) * ℓ := by positivity
        have h3 := pow_le_pow_left₀ hmℓ0 hmℓ 3
        rwa [mul_pow] at h3
      calc
        (m : ℝ) ^ 3 * (n : ℝ) ≤ (m : ℝ) ^ 3 * (ρmax * ℓ ^ 3) :=
          mul_le_mul_of_nonneg_left hn' (pow_nonneg (by positivity) 3)
        _ = ρmax * ((m : ℝ) ^ 3 * ℓ ^ 3) := by ring
        _ ≤ ρmax * G ^ 3 := mul_le_mul_of_nonneg_left hG3 hρmax
    have hbal : boxEnergy N G v ≤ (m : ℝ) ^ 3 * boxEnergy n ℓ v := by
      have hb := boxEnergy_grid_balanced (m := m) (nbar := n) (N := N) hm hℓ hR hGpos hLbox
        (v := v) hv hv1 hsupp (show N ≤ m ^ 3 * n from le_rfl)
      simpa [N, Nat.cast_pow] using hb
    have hval : boxEnergy N G v - μ * (N : ℝ) ≤ (m : ℝ) ^ 3 * (boxEnergy n ℓ v - μ * (n : ℝ)) := by
      calc
        boxEnergy N G v - μ * (N : ℝ) ≤ (m : ℝ) ^ 3 * boxEnergy n ℓ v - μ * (N : ℝ) := by
          exact sub_le_sub_right hbal (μ * (N : ℝ))
        _ = (m : ℝ) ^ 3 * boxEnergy n ℓ v - (m : ℝ) ^ 3 * (μ * (n : ℝ)) := by
          rw [hcast]
          ring
        _ = (m : ℝ) ^ 3 * (boxEnergy n ℓ v - μ * (n : ℝ)) := by ring
    have hmem : boxEnergy N G v - μ * (N : ℝ) ∈ gcSet v μ ρmax G := ⟨N, hNad, rfl⟩
    exact le_trans (gcBox_le_value (μ := μ) (ρmax := ρmax) (L := G) hμ hρmax hGpos hv hNad) hval
  have hm3 : 0 < (m : ℝ) ^ 3 := by positivity
  have hdiv : gcBox v μ ρmax G / (m : ℝ) ^ 3 ≤ gcBox v μ ρmax ℓ := by
    apply le_csInf (gcSet_nonempty (μ := μ) hρmax hℓ.le)
    intro y hy
    have htmp : gcBox v μ ρmax G ≤ (m : ℝ) ^ 3 * y := hcore y hy
    rw [div_le_iff₀ hm3]
    simpa [mul_comm] using htmp
  calc
    gcBox v μ ρmax G = (gcBox v μ ρmax G / (m : ℝ) ^ 3) * (m : ℝ) ^ 3 := by
      field_simp [pow_ne_zero 3 (ne_of_gt hm3)]
    _ ≤ gcBox v μ ρmax ℓ * (m : ℝ) ^ 3 := by
      exact mul_le_mul_of_nonneg_right hdiv hm3.le
    _ = (m : ℝ) ^ 3 * gcBox v μ ρmax ℓ := by ring

/-! ## Monotonicity in the side length -/

/-- `gcBox` is non-increasing in the side length: `0 < L1 ≤ L2` implies
`gcBox(·,L2) ≤ gcBox(·,L1)`. -/
lemma gcBox_antitone {v : ℝ³ → ℝ} {μ ρmax L1 L2 : ℝ} (hμ : 0 ≤ μ) (hρmax : 0 ≤ ρmax)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hLL : L1 ≤ L2) (hv : 0 ≤ v) :
    gcBox v μ ρmax L2 ≤ gcBox v μ ρmax L1 := by
  -- S₁ := gcSet at L1 (admissible N ≤ ρmaxL1³), S₂ at L2: every S₁-value is ≥ a S₂-value
  apply sInf_le_sInf_of_le
  · exact gcSet_nonempty (μ := μ) hρmax hL1.le
  · exact gcSet_bddBelow (μ := μ) (ρmax := ρmax) (L := L2) hμ hρmax hL2 hv
  · intro a ha
    rcases ha with ⟨N, hNad, rfl⟩
    refine ⟨boxEnergy N L2 v - μ * (N : ℝ), ?_, ?_⟩
    · refine ⟨N, ?_, rfl⟩
      dsimp [gcAdmissible]
      have hpow : L1 ^ 3 ≤ L2 ^ 3 := pow_le_pow_left₀ hL1.le hLL 3
      have hN1 : (N : ℝ) ≤ ρmax * L1 ^ 3 := by
        dsimp [gcAdmissible] at hNad
        exact hNad
      calc
        (N : ℝ) ≤ ρmax * L1 ^ 3 := hN1
        _ ≤ ρmax * L2 ^ 3 := mul_le_mul_of_nonneg_left hpow hρmax
    · exact sub_le_sub_right (boxEnergy_antitone hL1 hLL hv) (μ * (N : ℝ))

/-! ## Two-sided bounds on the density `gcBox/L³` -/

/-- Lower bound: `gcBox(μ,ρmax,L) ≥ −μρmaxL³`. -/
lemma gcBox_ge {v : ℝ³ → ℝ} {μ ρmax L : ℝ} (hμ : 0 ≤ μ) (hρmax : 0 ≤ ρmax)
    (hL : 0 < L) (hv : 0 ≤ v) : -(μ * (ρmax * L ^ 3)) ≤ gcBox v μ ρmax L := by
  exact le_gcBox_of_forall (μ := μ) hρmax hL.le (by
    intro y hy
    rcases hy with ⟨N, hNad, rfl⟩
    have hE : 0 ≤ boxEnergy N L v := boxEnergy_nonneg hL hv
    have hN : μ * (N : ℝ) ≤ μ * (ρmax * L ^ 3) := by
      exact mul_le_mul_of_nonneg_left (by dsimp [gcAdmissible] at hNad; exact hNad) hμ
    nlinarith)

/-- Lower bound on the density: `gcBox(μ,ρmax,L)/L³ ≥ −μρmax`. -/
lemma gcBox_density_ge {v : ℝ³ → ℝ} {μ ρmax L : ℝ} (hμ : 0 ≤ μ) (hρmax : 0 ≤ ρmax)
    (hL : 0 < L) (hv : 0 ≤ v) : -(μ * ρmax) ≤ gcBox v μ ρmax L / L ^ 3 := by
  have hge := gcBox_ge (μ := μ) (ρmax := ρmax) (L := L) hμ hρmax hL hv
  calc
    -(μ * ρmax) = -(μ * (ρmax * L ^ 3)) / L ^ 3 := by
      field_simp [pow_ne_zero 3 (ne_of_gt hL)]
    _ ≤ gcBox v μ ρmax L / L ^ 3 :=
      div_le_div_of_nonneg_right hge (pow_nonneg hL.le 3)

/-- Upper bound on the density from the product trial state: for `0 ≤ ρmax`,
`gcBox(μ,ρmax,L)/L³ ≤ C(ρmax²‖v‖₁ + ρmax)` uniformly in `L ≥ 1`. -/
lemma gcBox_density_le_bound {v : ℝ³ → ℝ} {μ ρmax : ℝ} (hμ : 0 ≤ μ) (hv : 0 ≤ v)
    (hv1 : MemLp v 1) (hρmax : 0 ≤ ρmax) :
    ∃ C : ℝ, 0 < C ∧ ∀ {L : ℝ}, 1 ≤ L →
      gcBox v μ ρmax L / L ^ 3 ≤ C * (ρmax ^ 2 * vL1 v + ρmax) := by
  rcases boxDensity_upper_bound hv1 with ⟨C, hCpos, hbd⟩
  refine ⟨C, hCpos, ?_⟩
  intro L hL1
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  let N : ℕ := Nat.floor (ρmax * L ^ 3)
  have hNad : gcAdmissible ρmax L N := by
    dsimp [gcAdmissible, N]
    have hx0 : 0 ≤ ρmax * L ^ 3 := mul_nonneg hρmax (pow_nonneg hLpos.le 3)
    exact Nat.floor_le hx0
  have hgcle := gcBox_le_value (μ := μ) (ρmax := ρmax) (L := L) hμ hρmax hLpos hv hNad
  have hNdens : (N : ℝ) / L ^ 3 ≤ ρmax := by
    dsimp [N]
    have hx0 : 0 ≤ ρmax * L ^ 3 := mul_nonneg hρmax (pow_nonneg hLpos.le 3)
    have hfl : (Nat.floor (ρmax * L ^ 3) : ℝ) ≤ ρmax * L ^ 3 := Nat.floor_le hx0
    rwa [div_le_iff₀ (pow_pos hLpos 3)]
  have hEbd := hbd ρmax N (L := L) hL1 hρmax hNdens
  have hμN : 0 ≤ μ * (N : ℝ) := mul_nonneg hμ (by exact_mod_cast Nat.zero_le N)
  calc
    gcBox v μ ρmax L / L ^ 3 ≤ (boxEnergy N L v - μ * (N : ℝ)) / L ^ 3 :=
      div_le_div_of_nonneg_right hgcle (pow_nonneg hLpos.le 3)
    _ ≤ boxEnergy N L v / L ^ 3 := by
      have hsub : boxEnergy N L v - μ * (N : ℝ) ≤ boxEnergy N L v := by linarith
      exact div_le_div_of_nonneg_right hsub (pow_nonneg hLpos.le 3)
    _ ≤ C * (ρmax ^ 2 * vL1 v + ρmax) := hEbd

end BoseGases

end Submission
