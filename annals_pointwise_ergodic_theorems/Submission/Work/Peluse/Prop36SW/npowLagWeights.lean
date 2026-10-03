import Mathlib
import Submission.Work.Peluse.Prop36SW.npowOneCollapseLe
import Submission.Work.Peluse.Prop36SW.npowOneEqPsi
import Submission.Work.Peluse.Prop36SW.corrEqZeroOfSupportIn

/-!
# The lag-weight comparison for the normalised box-norm power

For a `1`-bounded function `f` supported in `[-M,M]`, `W := 2M+1` and `L ≥ W`, the `ψ_L`-weighted
lag sum of the level-`t` box-norm powers of the "difference functions"
`y ↦ f y · conj (f (y + m))` is bounded by a constant (independent of `L`, `M`, `f`, and `t`)
times the `ψ_W`-weighted one.  Here `ψ_H(m) = (H-|m|)/H` is the triangular (Fejér) kernel.

The proof is a recursion in the level `t`.

* **Level `1`.**  Unwinding `Npow 1` as a `ψ`-sum of correlations (`npowOneEqPsi`) and using the
  symmetry `corr (f · conj(f(·+m))) d = corr (f · conj(f(·+d))) m` (`TransferUp.corr_symm`), the two
  sides are the *transposes* of each other: the `ψ_L` weight sits on the `m`-lag on the left and on
  the `d`-lag on the right, the double sum being symmetric.  Bounding the `L`-scale `ψ`-sum by the
  `W`-scale one for each fixed inner function is exactly the level-`1` collapse
  (`uNormPow_one_collapse`, via `npowOneCollapseLe`), and the vanishing of the correlations beyond
  the lag `2M` (`corrEqZeroOfSupportIn`) lets the inner sum be extended from the `W`-index set to
  the `L`-index set.

* **Level `t+1`.**  Expanding `Npow (t+1)` with the peel recursion `TransferUp.Npow_succ` turns the
  summand into `Npow t` of `y ↦ F y · conj (F (y+e))` for `F = f · conj(f(·+m))`; the elementary
  identity `lagFn_lagFn` identifies this with `Npow t` of the difference function of the `1`-bounded
  function `G_e = f · conj(f(·+e))`, to which the induction hypothesis at level `t` applies.

The constant produced is the one of the level-`1` collapse, uniformly in `t`.
-/

set_option maxHeartbeats 4000000

open scoped BigOperators

namespace Work.Peluse.Prop36SW

open Work.Peluse
open Work.Peluse.TransferUp

/-- The lag index set `{-(N-1), …, N-1}`.  The target statement uses it with `N = 2*M+1`. -/
noncomputable def lagIccN (N : ℕ) : Finset ℤ := Finset.Icc (-(N : ℤ) + 1) ((N : ℤ) - 1)

/-- The difference function `y ↦ f y · conj (f (y + m))` attached to the lag `m`. -/
def lagFn (f : ℤ → ℂ) (m : ℤ) : ℤ → ℂ := fun y => f y * star (f (y + m))

/-- Definitional unfolding of `lagFn`, used to convert the internal formulation back to the
explicit function of the statement. -/
lemma lagFn_eq (f : ℤ → ℂ) (m : ℤ) : lagFn f m = fun y : ℤ => f y * star (f (y + m)) := rfl

/-- Pointwise unfolding of `lagFn`. -/
private lemma lagFn_apply (f : ℤ → ℂ) (m y : ℤ) : lagFn f m y = f y * star (f (y + m)) := rfl

/-- The correlation symmetry in the `lagFn` vocabulary. -/
private lemma corr_lagFn_symm (f : ℤ → ℂ) (a b : ℤ) :
    corr (lagFn f a) b = corr (lagFn f b) a := corr_symm f a b

/-- **The elementary identity of the recursion.**  Taking the difference function of the difference
function `f · conj(f(·+e))` at the lag `m` is the same as taking `F_m · conj(F_m (·+e))` for
`F_m = f · conj(f(·+m))`: both products collect the four values `f y`, `conj (f (y+m))`,
`conj (f (y+e))`, `f (y+m+e)`. -/
private lemma lagFn_lagFn (f : ℤ → ℂ) (m e : ℤ) :
    lagFn (lagFn f e) m = fun y : ℤ => lagFn f m y * star (lagFn f m (y + e)) := by
  funext y
  have hadd : (y + e) + m = (y + m) + e := by ring
  simp only [lagFn_apply, star_mul, star_star, hadd]
  ring

/-- The support of a difference function is contained in the support of the underlying function. -/
private lemma supportInLagFn {M : ℕ} {f : ℤ → ℂ} (hsup : SupportIn f M) (m : ℤ) :
    SupportIn (lagFn f m) M := by
  intro x hx
  show f x * star (f (x + m)) = 0
  rw [hsup x hx, zero_mul]

/-- Difference functions of a `1`-bounded function are `1`-bounded. -/
private lemma normLagFn {f : ℤ → ℂ} (hb : ∀ x : ℤ, ‖f x‖ ≤ 1) (m : ℤ) :
    ∀ x : ℤ, ‖lagFn f m x‖ ≤ 1 := by
  intro x
  show ‖f x * star (f (x + m))‖ ≤ 1
  rw [norm_mul, norm_star]
  exact mul_le_one₀ (hb x) (norm_nonneg _) (hb _)

/-- The lag index sets are nested in the scale. -/
private lemma lagIccN_subset {N N' : ℕ} (h : N ≤ N') : lagIccN N ⊆ lagIccN N' := by
  intro m hm
  simp only [lagIccN, Finset.mem_Icc] at hm ⊢
  omega

/-- A lag outside `lagIccN (2*M+1)` is at distance at least `2M+1`. -/
private lemma lagIccN_not_mem {M : ℕ} {m : ℤ} (hm : m ∉ lagIccN (2 * M + 1)) :
    2 * M + 1 ≤ m.natAbs := by
  have hm2 : ¬ ((-(((2 * M + 1 : ℕ) : ℤ)) + 1 ≤ m) ∧ (m ≤ (((2 * M + 1 : ℕ)) : ℤ) - 1)) := by
    simpa only [lagIccN, Finset.mem_Icc] using hm
  rcases not_and_or.mp hm2 with h | h
  · have h1 : m < -(((2 * M + 1 : ℕ) : ℤ)) + 1 := not_le.mp h
    have h2 : ((2 * M + 1 : ℕ) : ℤ) ≤ -m := by omega
    have h3 := Int.le_natAbs (a := -m)
    rw [Int.natAbs_neg] at h3
    omega
  · have h1 : (((2 * M + 1 : ℕ) : ℤ)) - 1 < m := not_le.mp h
    have h2 : ((2 * M + 1 : ℕ) : ℤ) ≤ m := by omega
    have h3 := Int.le_natAbs (a := m)
    omega

/-- The statement of the lag-weight comparison at level `t`. -/
noncomputable def LagIneq (t : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (L M : ℕ) (f : ℤ → ℂ), 1 ≤ M → 2 * M + 1 ≤ L →
    Work.Peluse.SupportIn f M → (∀ x : ℤ, ‖f x‖ ≤ 1) →
      (∑ m ∈ lagIccN (2 * M + 1), psi L m *
          Npow t (fun _ : Fin t => (1 : ℤ)) (symIcc M) (lagFn f m) (2 * M + 1))
      ≤ C * (∑ m ∈ lagIccN (2 * M + 1), psi (2 * M + 1) m *
          Npow t (fun _ : Fin t => (1 : ℤ)) (symIcc M) (lagFn f m) (2 * M + 1))

/-- **The base case `t = 1.`**  Both sides of the `t = 1` inequality are the same double sum of
§(lag, correlation) pairs, with the two `ψ`-weights interchanged; the lag symmetry
`TransferUp.corr_symm` makes the interchange legitimate, and the level-`1` collapse bounds the
`L`-scale `ψ`-sum by the `W`-scale one. -/
private lemma baseCase : LagIneq 1 := by
  obtain ⟨C, hC, hcol⟩ := npowOneCollapseLe
  refine ⟨C, hC, ?_⟩
  intro L M f hM hLM hsup hb
  have hS : 0 < (symIcc M).card := by
    rw [Work.Peluse.symIcc]; exact Finset.card_pos.mpr ⟨0, by simp⟩
  have hfind : ∀ d : ℤ, Work.Peluse.FinSuppZ (lagFn f d) :=
    fun d => Work.Peluse.FinSuppZ.of_supportIn (supportInLagFn hsup d)
  have hN : ∀ m : ℤ, Npow 1 (fun _ : Fin 1 => (1 : ℤ)) (symIcc M) (lagFn f m) (2 * M + 1)
      = ∑ d ∈ lagIccN (2 * M + 1), psi (2 * M + 1) d * (corr (lagFn f m) d).re := by
    intro m
    rw [npowOneEqPsi (S := symIcc M) hS (lagFn f m) (hfind m) (2 * M + 1)]
    rfl
  have hswap : (∑ m ∈ lagIccN (2 * M + 1), ∑ d ∈ lagIccN (2 * M + 1),
        psi L m * (psi (2 * M + 1) d * (corr (lagFn f m) d).re))
      = ∑ d ∈ lagIccN (2 * M + 1), ∑ m ∈ lagIccN (2 * M + 1),
        psi (2 * M + 1) d * (psi L m * (corr (lagFn f d) m).re) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun m _ => ?_))
    rw [corr_lagFn_symm f m d]
    ring
  have hext : ∀ d : ℤ, (∑ m ∈ lagIccN (2 * M + 1), psi L m * (corr (lagFn f d) m).re)
      = ∑ m ∈ lagIccN L, psi L m * (corr (lagFn f d) m).re := by
    intro d
    refine Finset.sum_subset (lagIccN_subset hLM) ?_
    intro m _ hm
    rw [corrEqZeroOfSupportIn (supportInLagFn hsup d) (lagIccN_not_mem hm)]
    simp
  have hL : ∀ d : ℤ, (∑ m ∈ lagIccN L, psi L m * (corr (lagFn f d) m).re)
      = Npow 1 (fun _ : Fin 1 => (1 : ℤ)) (symIcc M) (lagFn f d) L := by
    intro d
    rw [npowOneEqPsi (S := symIcc M) hS (lagFn f d) (hfind d) L]
    rfl
  calc (∑ m ∈ lagIccN (2 * M + 1), psi L m *
        Npow 1 (fun _ : Fin 1 => (1 : ℤ)) (symIcc M) (lagFn f m) (2 * M + 1))
      = ∑ m ∈ lagIccN (2 * M + 1), psi L m *
          (∑ d ∈ lagIccN (2 * M + 1), psi (2 * M + 1) d *
            (corr (lagFn f m) d).re) := by
        refine Finset.sum_congr rfl (fun m _ => ?_); rw [hN m]
    _ = ∑ m ∈ lagIccN (2 * M + 1), ∑ d ∈ lagIccN (2 * M + 1), psi L m *
          (psi (2 * M + 1) d * (corr (lagFn f m) d).re) := by
        refine Finset.sum_congr rfl (fun m _ => ?_); rw [Finset.mul_sum]
    _ = ∑ d ∈ lagIccN (2 * M + 1), ∑ m ∈ lagIccN (2 * M + 1), psi (2 * M + 1) d *
          (psi L m * (corr (lagFn f d) m).re) := hswap
    _ = ∑ d ∈ lagIccN (2 * M + 1), psi (2 * M + 1) d *
          (∑ m ∈ lagIccN (2 * M + 1), psi L m * (corr (lagFn f d) m).re) := by
        refine Finset.sum_congr rfl (fun d _ => ?_); rw [Finset.mul_sum]
    _ = ∑ d ∈ lagIccN (2 * M + 1), psi (2 * M + 1) d *
          (∑ m ∈ lagIccN L, psi L m * (corr (lagFn f d) m).re) := by
        refine Finset.sum_congr rfl (fun d _ => ?_); rw [hext d]
    _ = ∑ d ∈ lagIccN (2 * M + 1), psi (2 * M + 1) d *
          Npow 1 (fun _ : Fin 1 => (1 : ℤ)) (symIcc M) (lagFn f d) L := by
        refine Finset.sum_congr rfl (fun d _ => ?_); rw [hL d]
    _ ≤ ∑ d ∈ lagIccN (2 * M + 1), psi (2 * M + 1) d *
          (C * Npow 1 (fun _ : Fin 1 => (1 : ℤ)) (symIcc M) (lagFn f d) (2 * M + 1)) := by
        refine Finset.sum_le_sum (fun d _ => ?_)
        exact mul_le_mul_of_nonneg_left
          (hcol L M (lagFn f d) hM hLM (supportInLagFn hsup d) (normLagFn hb d))
          (psi_nonneg (2 * M + 1) d)
    _ = C * (∑ d ∈ lagIccN (2 * M + 1), psi (2 * M + 1) d *
          Npow 1 (fun _ : Fin 1 => (1 : ℤ)) (symIcc M) (lagFn f d) (2 * M + 1)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun d _ => ?_); ring
    _ = C * (∑ m ∈ lagIccN (2 * M + 1), psi (2 * M + 1) m *
          Npow 1 (fun _ : Fin 1 => (1 : ℤ)) (symIcc M) (lagFn f m) (2 * M + 1)) := rfl

/-- **The recursion step.**  The peel recursion `Npow_succ` writes the level-`(t+1)` lag weight in
terms of level-`t` objects of the difference functions, and the identity `lagFn_lagFn` turns those
into difference functions of the `1`-bounded function `f · conj(f(·+e))`, to which the induction
hypothesis applies.  The constant is unchanged. -/
private lemma stepCase (k : ℕ) (hk : 1 ≤ k) (h : LagIneq k) : LagIneq (k + 1) := by
  obtain ⟨C, hC, hineq⟩ := h
  refine ⟨C, hC, ?_⟩
  intro L M f hM hLM hsup hb
  have hW1 : 1 ≤ 2 * M + 1 := by omega
  have hfind : ∀ d : ℤ, Work.Peluse.FinSuppZ (lagFn f d) :=
    fun d => Work.Peluse.FinSuppZ.of_supportIn (supportInLagFn hsup d)
  have hNs : ∀ m : ℤ, Npow (k + 1) (fun _ : Fin (k + 1) => (1 : ℤ)) (symIcc M) (lagFn f m) (2 * M + 1)
      = ∑ e ∈ lagIccN (2 * M + 1), psi (2 * M + 1) e *
          Npow k (fun _ : Fin k => (1 : ℤ)) (symIcc M)
            (fun y : ℤ => lagFn f m y * star (lagFn f m (y + e))) (2 * M + 1) := by
    intro m
    rw [Npow_succ hk (fun _ : Fin (k + 1) => (1 : ℤ)) (by norm_num) (symIcc M) (lagFn f m)
      (hfind m) hW1]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    have h1 : (fun i : Fin k => (fun _ : Fin (k + 1) => (1 : ℤ)) i.succ)
        = (fun _ : Fin k => (1 : ℤ)) := by
      funext i; rfl
    have h2 : (fun y : ℤ => lagFn f m y * star (lagFn f m (y + (fun _ : Fin (k + 1) => (1 : ℤ)) 0 * e)))
        = (fun y : ℤ => lagFn f m y * star (lagFn f m (y + e))) := by
      funext y; simp
    rw [h1, h2]
  have hfac : ∀ (Z : ℤ → ℝ), (∑ e ∈ lagIccN (2 * M + 1), psi (2 * M + 1) e * (C * Z e))
      = C * (∑ e ∈ lagIccN (2 * M + 1), psi (2 * M + 1) e * Z e) := by
    intro Z
    have h1 : (∑ e ∈ lagIccN (2 * M + 1), psi (2 * M + 1) e * (C * Z e))
        = ∑ e ∈ lagIccN (2 * M + 1), C * (psi (2 * M + 1) e * Z e) :=
      Finset.sum_congr rfl (fun e _ => by ring)
    exact h1.trans (Finset.mul_sum _ (fun e => psi (2 * M + 1) e * Z e) C).symm
  have hswap2 : (∑ e ∈ lagIccN (2 * M + 1), psi (2 * M + 1) e *
        (∑ m ∈ lagIccN (2 * M + 1), psi (2 * M + 1) m *
          Npow k (fun _ : Fin k => (1 : ℤ)) (symIcc M) (lagFn (lagFn f e) m) (2 * M + 1)))
      = ∑ m ∈ lagIccN (2 * M + 1), psi (2 * M + 1) m *
        (∑ e ∈ lagIccN (2 * M + 1), psi (2 * M + 1) e *
          Npow k (fun _ : Fin k => (1 : ℤ)) (symIcc M) (lagFn (lagFn f e) m) (2 * M + 1)) := by
    calc (∑ e ∈ lagIccN (2 * M + 1), psi (2 * M + 1) e *
          (∑ m ∈ lagIccN (2 * M + 1), psi (2 * M + 1) m *
            Npow k (fun _ : Fin k => (1 : ℤ)) (symIcc M) (lagFn (lagFn f e) m) (2 * M + 1)))
        = ∑ e ∈ lagIccN (2 * M + 1), ∑ m ∈ lagIccN (2 * M + 1), psi (2 * M + 1) e *
            (psi (2 * M + 1) m * Npow k (fun _ : Fin k => (1 : ℤ)) (symIcc M)
              (lagFn (lagFn f e) m) (2 * M + 1)) :=
          Finset.sum_congr rfl (fun e _ => Finset.mul_sum _ _ _)
      _ = ∑ m ∈ lagIccN (2 * M + 1), ∑ e ∈ lagIccN (2 * M + 1), psi (2 * M + 1) m *
            (psi (2 * M + 1) e * Npow k (fun _ : Fin k => (1 : ℤ)) (symIcc M)
              (lagFn (lagFn f e) m) (2 * M + 1)) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun e _ => by ring))
      _ = ∑ m ∈ lagIccN (2 * M + 1), psi (2 * M + 1) m *
            (∑ e ∈ lagIccN (2 * M + 1), psi (2 * M + 1) e *
              Npow k (fun _ : Fin k => (1 : ℤ)) (symIcc M) (lagFn (lagFn f e) m) (2 * M + 1)) :=
          Finset.sum_congr rfl (fun m _ => (Finset.mul_sum _ _ _).symm)
  calc (∑ m ∈ lagIccN (2 * M + 1), psi L m *
        Npow (k + 1) (fun _ : Fin (k + 1) => (1 : ℤ)) (symIcc M) (lagFn f m) (2 * M + 1))
      = ∑ m ∈ lagIccN (2 * M + 1), ∑ e ∈ lagIccN (2 * M + 1), psi L m *
          (psi (2 * M + 1) e * Npow k (fun _ : Fin k => (1 : ℤ)) (symIcc M)
            (fun y : ℤ => lagFn f m y * star (lagFn f m (y + e))) (2 * M + 1)) := by
        refine Finset.sum_congr rfl (fun m _ => ?_)
        rw [hNs m, Finset.mul_sum]
    _ = ∑ m ∈ lagIccN (2 * M + 1), ∑ e ∈ lagIccN (2 * M + 1), psi L m *
          (psi (2 * M + 1) e * Npow k (fun _ : Fin k => (1 : ℤ)) (symIcc M)
            (lagFn (lagFn f e) m) (2 * M + 1)) := by
        refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun e _ => ?_))
        rw [← lagFn_lagFn f m e]
    _ = ∑ e ∈ lagIccN (2 * M + 1), ∑ m ∈ lagIccN (2 * M + 1), psi (2 * M + 1) e *
          (psi L m * Npow k (fun _ : Fin k => (1 : ℤ)) (symIcc M)
            (lagFn (lagFn f e) m) (2 * M + 1)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun m _ => ?_))
        ring
    _ = ∑ e ∈ lagIccN (2 * M + 1), psi (2 * M + 1) e *
          (∑ m ∈ lagIccN (2 * M + 1), psi L m *
            Npow k (fun _ : Fin k => (1 : ℤ)) (symIcc M) (lagFn (lagFn f e) m) (2 * M + 1)) :=
        Finset.sum_congr rfl (fun e _ => (Finset.mul_sum _ _ _).symm)
    _ ≤ ∑ e ∈ lagIccN (2 * M + 1), psi (2 * M + 1) e *
          (C * ∑ m ∈ lagIccN (2 * M + 1), psi (2 * M + 1) m *
            Npow k (fun _ : Fin k => (1 : ℤ)) (symIcc M) (lagFn (lagFn f e) m) (2 * M + 1)) := by
        refine Finset.sum_le_sum (fun e _ => ?_)
        exact mul_le_mul_of_nonneg_left
          (hineq L M (lagFn f e) hM hLM (supportInLagFn hsup e) (normLagFn hb e))
          (psi_nonneg (2 * M + 1) e)
    _ = C * (∑ m ∈ lagIccN (2 * M + 1), psi (2 * M + 1) m *
          (∑ e ∈ lagIccN (2 * M + 1), psi (2 * M + 1) e *
            Npow k (fun _ : Fin k => (1 : ℤ)) (symIcc M) (lagFn (lagFn f e) m) (2 * M + 1))) := by
        rw [hfac]
        exact congrArg (fun z => C * z) hswap2
    _ = C * (∑ m ∈ lagIccN (2 * M + 1), psi (2 * M + 1) m *
          (∑ e ∈ lagIccN (2 * M + 1), psi (2 * M + 1) e *
            Npow k (fun _ : Fin k => (1 : ℤ)) (symIcc M)
              (fun y : ℤ => lagFn f m y * star (lagFn f m (y + e))) (2 * M + 1))) := by
        refine congrArg (fun z => C * z) ?_
        refine Finset.sum_congr rfl (fun m _ => ?_)
        congr 1
        refine Finset.sum_congr rfl (fun e _ => ?_)
        rw [lagFn_lagFn f m e]
    _ = C * (∑ m ∈ lagIccN (2 * M + 1), psi (2 * M + 1) m *
          Npow (k + 1) (fun _ : Fin (k + 1) => (1 : ℤ)) (symIcc M) (lagFn f m) (2 * M + 1)) := by
        refine congrArg (fun z => C * z) ?_
        refine Finset.sum_congr rfl (fun m _ => ?_)
        rw [hNs m, Finset.mul_sum]

/-- All levels at once, by induction on the level. -/
theorem npowLagWeights_aux (t : ℕ) (ht : 1 ≤ t) : LagIneq t :=
  Nat.le_induction baseCase (fun k hk ih => stepCase k hk ih) t ht

theorem npowLagWeights {t : ℕ} (ht : 1 ≤ t) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L M : ℕ) (f : ℤ → ℂ), 1 ≤ M → 2 * M + 1 ≤ L →
      Work.Peluse.SupportIn f M → (∀ x : ℤ, ‖f x‖ ≤ 1) →
        (∑ m ∈ Finset.Icc (-(((2 * M + 1 : ℕ) : ℤ)) + 1) ((((2 * M + 1 : ℕ)) : ℤ) - 1),
            Work.Peluse.TransferUp.psi L m *
              Work.Peluse.TransferUp.Npow t (fun _ : Fin t => (1 : ℤ)) (Work.Peluse.symIcc M)
                (fun y : ℤ => f y * star (f (y + m))) (2 * M + 1))
          ≤ C * (∑ m ∈ Finset.Icc (-(((2 * M + 1 : ℕ) : ℤ)) + 1) ((((2 * M + 1 : ℕ)) : ℤ) - 1),
              Work.Peluse.TransferUp.psi (2 * M + 1) m *
                Work.Peluse.TransferUp.Npow t (fun _ : Fin t => (1 : ℤ)) (Work.Peluse.symIcc M)
                  (fun y : ℤ => f y * star (f (y + m))) (2 * M + 1)) := by
  have h := npowLagWeights_aux t ht
  simpa only [LagIneq, lagIccN, lagFn_eq] using h

end Work.Peluse.Prop36SW
