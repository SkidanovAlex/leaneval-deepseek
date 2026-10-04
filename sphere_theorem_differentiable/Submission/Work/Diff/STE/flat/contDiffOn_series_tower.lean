import Mathlib
import Submission.Work.Diff.STE.flat.TowerDefs
import Submission.Work.Diff.EXT.hasFTaylorSeriesUpToOn_tsum_gen
import Submission.Work.Diff.STE.flat.hasFTaylorSeriesUpToOn_tower
import Submission.Work.Diff.STE.flat.norm_iteratedFDerivWithin_fourierExp_snd_le
import Submission.Work.Diff.STE.flat.norm_iteratedFDerivWithin_tower_fst_le
import Submission.Work.Diff.STE.contDiff_seriesFun
import Submission.Work.Diff.STE.summable_wt_zpow

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Joint `C^∞` of a Fourier series whose coefficient tower is a time-derivative tower

This file proves `Work.Diff.STE.flat.contDiffOn_series_tower`: given a family of matrix-valued
Fourier coefficient families `d j t k` of the flat torus `(Fin n → ℝ)`, uniformly rapidly decaying
in the frequency `k` (`hd`) and forming a time-derivative tower (`ht`: `∂_t (d j · k) = d (j+1) · k`
within `Ico 0 τ`), the function

`(t, x) ↦ seriesFunM (d 0 t) x = ∑'_k (d 0 t k) · exp (2π i k·x)`

is `C^∞` on the slab `Ico 0 τ × univ`.

The proof transfers the smoothness of the one-variable tower (`hasFTaylorSeriesUpToOn_tower`) through
the rapidly convergent Fourier series (`hasFTaylorSeriesUpToOn_tsum_gen`), one matrix entry at a
time; the summable majorants are multiples of `⟨k⟩^{-(n+1)}` (`summable_wt_zpow`).
-/

namespace Work.Diff.STE.flat

open Set Filter
open scoped BigOperators Topology ContDiff
open Work.Diff.STE.Flat

noncomputable section

variable {n : ℕ}

/-- The slab `Ico 0 τ × univ` of `ℝ × (Fin n → ℝ)` is convex. -/
theorem convex_slab (τ : ℝ) :
    Convex ℝ (Set.Ico (0 : ℝ) τ ×ˢ (Set.univ : Set (Fin n → ℝ))) :=
  (convex_Ico 0 τ).prod convex_univ

/-- The slab `Ico 0 τ × univ` has nonempty interior (for `τ > 0`). -/
theorem interior_slab_nonempty (τ : ℝ) (hτ : 0 < τ) :
    (interior (Set.Ico (0 : ℝ) τ ×ˢ (Set.univ : Set (Fin n → ℝ)))).Nonempty := by
  rw [interior_prod_eq, interior_Ico, interior_univ]
  refine ⟨(τ / 2, 0), ?_, trivial⟩
  simp only [mem_Ioo]
  constructor <;> linarith

/-- The slab `Ico 0 τ × univ` is a set of uniqueness (for `τ > 0`). -/
theorem uniqueDiffOn_slab (τ : ℝ) (hτ : 0 < τ) :
    UniqueDiffOn ℝ (Set.Ico (0 : ℝ) τ ×ˢ (Set.univ : Set (Fin n → ℝ))) :=
  uniqueDiffOn_convex (convex_slab (n := n) τ) (interior_slab_nonempty (n := n) τ hτ)

/-- A one-variable derivative tower, transported to the product `ℝ × Y`: the function
`p ↦ c 0 p.1` is `C^N` on the slab. -/
theorem contDiffOn_tower_fst {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (τ : ℝ) {c : ℕ → ℝ → V}
    (h : ∀ j, ∀ t ∈ Set.Ico (0 : ℝ) τ,
      HasDerivWithinAt (c j) (c (j + 1) t) (Set.Ico (0 : ℝ) τ) t) (N : ℕ) :
    ContDiffOn ℝ (N : ℕ∞) (fun p : ℝ × Y => c 0 p.1)
      (Set.Ico (0 : ℝ) τ ×ˢ (Set.univ : Set Y)) := by
  have hcd : ContDiffOn ℝ (N : ℕ∞) (c 0) (Set.Ico (0 : ℝ) τ) :=
    (hasFTaylorSeriesUpToOn_tower (I := Set.Ico (0 : ℝ) τ) (convex_Ico 0 τ) h N).contDiffOn
  exact hcd.comp ((ContinuousLinearMap.fst ℝ ℝ Y).contDiff.contDiffOn) (fun p hp => hp.1)

/-- The scalar constant multiplying `⟨m⟩^{-(n+1)}` in the majorant. -/
def majConst (C : ℕ → ℝ) (n k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * C i * (2 * Real.pi * (n : ℝ) + 1) ^ k

/-- The summable majorant for the `k`-th derivative of the summands. -/
def majFun (C : ℕ → ℝ) (n k : ℕ) (m : Fin n → ℤ) : ℝ :=
  majConst C n k * (Work.Diff.STE.wt m) ^ (-((n + 1 : ℕ) : ℤ))

/-- **The matrix entry of the series is `C^N` on the slab.** -/
theorem contDiffOn_series_component (τ : ℝ) (hτ : 0 < τ)
    (d : ℕ → ℝ → (Fin n → ℤ) → MatC n)
    (hd : ∀ j M, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico (0 : ℝ) τ, ∀ k : Fin n → ℤ, ∀ a b : Fin n,
      ‖d j t k a b‖ * (wt k) ^ M ≤ C)
    (ht : ∀ j, ∀ t ∈ Set.Ico (0 : ℝ) τ, ∀ k : Fin n → ℤ, ∀ a b : Fin n,
      HasDerivWithinAt (fun s : ℝ => d j s k a b) (d (j + 1) t k a b) (Set.Ico (0 : ℝ) τ) t)
    (a b : Fin n) (N : ℕ) :
    ContDiffOn ℝ (N : ℕ∞)
      (fun p : ℝ × (Fin n → ℝ) => seriesFunM (d 0 p.1) p.2 a b)
      (Set.Ico (0 : ℝ) τ ×ˢ Set.univ) := by
  classical
  choose C hC using fun j : ℕ => hd j (2 * N + n + 1)
  have hCnn : ∀ j, 0 ≤ C j := fun j => (hC j).1
  have hCbd : ∀ j, ∀ t ∈ Set.Ico (0 : ℝ) τ, ∀ k : Fin n → ℤ, ∀ a b : Fin n,
      ‖d j t k a b‖ * (wt k) ^ (2 * N + n + 1) ≤ C j := fun j => (hC j).2
  have hAnn : ∀ k, 0 ≤ majConst C n k := by
    intro k
    rw [majConst]
    refine Finset.sum_nonneg fun i hi => ?_
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hCnn i)) (by positivity)
  have hv : ∀ k ≤ N, Summable (fun m : Fin n → ℤ => majFun C n k m) := by
    intro k hk
    have hcard : Fintype.card (Fin n) < 2 * (n + 1) := by rw [Fintype.card_fin]; omega
    have h := (summable_wt_zpow (n + 1) hcard).mul_left (majConst C n k)
    simpa only [majFun] using h
  have hfac1 : ∀ m : Fin n → ℤ, ContDiffOn ℝ (N : ℕ∞)
      (fun p : ℝ × (Fin n → ℝ) => d 0 p.1 m a b) (Set.Ico (0 : ℝ) τ ×ˢ Set.univ) := by
    intro m
    exact contDiffOn_tower_fst τ (c := fun j t => d j t m a b)
      (fun j t ht' => ht j t ht' m a b) N
  have hfac2 : ∀ m : Fin n → ℤ, ContDiffOn ℝ (N : ℕ∞)
      (fun p : ℝ × (Fin n → ℝ) => fourierExp m p.2) (Set.Ico (0 : ℝ) τ ×ˢ Set.univ) := by
    intro m
    exact ((contDiff_fourierExp_top m).comp
      ((ContinuousLinearMap.snd ℝ ℝ (Fin n → ℝ)).contDiff)).contDiffOn.of_le le_top
  have hf : ∀ m : Fin n → ℤ, ContDiffOn ℝ (N : ℕ∞)
      (fun p : ℝ × (Fin n → ℝ) => d 0 p.1 m a b * fourierExp m p.2)
      (Set.Ico (0 : ℝ) τ ×ˢ Set.univ) := fun m => (hfac1 m).mul (hfac2 m)
  have hseries : ∀ m : Fin n → ℤ, HasFTaylorSeriesUpToOn (N : ℕ∞) (fun t : ℝ => d 0 t m a b)
      (fun t j => ContinuousMultilinearMap.mkPiRing ℝ (Fin j) (d j t m a b))
      (Set.Ico (0 : ℝ) τ) := fun m =>
    hasFTaylorSeriesUpToOn_tower (I := Set.Ico (0 : ℝ) τ) (convex_Ico 0 τ)
      (fun j t ht' => ht j t ht' m a b) N
  have hbnd : ∀ (k : ℕ), k ≤ N → ∀ (m : Fin n → ℤ), ∀ p ∈ Set.Ico (0 : ℝ) τ ×ˢ Set.univ,
      ‖iteratedFDerivWithin ℝ k
        (fun p : ℝ × (Fin n → ℝ) => d 0 p.1 m a b * fourierExp m p.2)
        (Set.Ico (0 : ℝ) τ ×ˢ Set.univ) p‖ ≤ majFun C n k m := by
    intro k hk m p hp
    have hp1 : p.1 ∈ Set.Ico (0 : ℝ) τ := hp.1
    have hk' : (k : ℕ∞ω) ≤ (N : ℕ∞ω) := by exact_mod_cast hk
    have hmul := norm_iteratedFDerivWithin_mul_le (𝕜 := ℝ) (A := ℂ)
      (f := fun p : ℝ × (Fin n → ℝ) => d 0 p.1 m a b)
      (g := fun p : ℝ × (Fin n → ℝ) => fourierExp m p.2)
      (hfac1 m) (hfac2 m) (uniqueDiffOn_slab (n := n) τ hτ) hp hk'
    have hw1 : (1 : ℝ) ≤ wt m := wt_one_le m
    have hw0 : (0 : ℝ) < wt m := wt_pos m
    have hS := uniqueDiffOn_slab (n := n) τ hτ
    have hterm : ∀ i ∈ Finset.range (k + 1),
        (k.choose i : ℝ) *
            ‖iteratedFDerivWithin ℝ i (fun p : ℝ × (Fin n → ℝ) => d 0 p.1 m a b)
              (Set.Ico (0 : ℝ) τ ×ˢ Set.univ) p‖ *
          ‖iteratedFDerivWithin ℝ (k - i) (fun p : ℝ × (Fin n → ℝ) => fourierExp m p.2)
              (Set.Ico (0 : ℝ) τ ×ˢ Set.univ) p‖
        ≤ (k.choose i : ℝ) * C i * (2 * Real.pi * (n : ℝ) + 1) ^ k *
            (wt m) ^ ((k : ℤ) - ((2 * N + n + 1 : ℕ) : ℤ)) := by
      intro i hi
      have hik : i ≤ k := Finset.mem_range_succ_iff.mp hi
      have h1 : ‖iteratedFDerivWithin ℝ i (fun p : ℝ × (Fin n → ℝ) => d 0 p.1 m a b)
            (Set.Ico (0 : ℝ) τ ×ˢ Set.univ) p‖
          ≤ C i * (wt m) ^ (-((2 * N + n + 1 : ℕ) : ℤ)) := by
        have hid' : ∀ t ∈ Set.Ico (0 : ℝ) τ,
            iteratedFDerivWithin ℝ i (fun t : ℝ => d 0 t m a b) (Set.Ico (0 : ℝ) τ) t
              = ContinuousMultilinearMap.mkPiRing ℝ (Fin i) (d i t m a b) := by
          intro t ht'
          exact ((hseries m).eq_iteratedFDerivWithin_of_uniqueDiffOn
            (m := i) (by exact_mod_cast (le_trans hik hk)) (uniqueDiffOn_Ico 0 τ) ht').symm
        have hcd : ContDiffOn ℝ (i : ℕ∞) (fun t : ℝ => d 0 t m a b) (Set.Ico (0 : ℝ) τ) :=
          contDiffOn_iff_forall_nat_le.mp (hseries m).contDiffOn i
            (by exact_mod_cast (le_trans hik hk))
        have hD := norm_iteratedFDerivWithin_tower_fst_le (Y := Fin n → ℝ)
          (uniqueDiffOn_Ico 0 τ) hS (c := fun j t => d j t m a b)
          (w := fun j t => d j t m a b) (k := i) hcd hid' p hp
        refine hD.trans ?_
        have hb := hCbd i p.1 hp1 m a b
        have hpow : (0 : ℝ) < (wt m) ^ (2 * N + n + 1) := pow_pos hw0 _
        have h2 : ‖d i p.1 m a b‖ ≤ C i / (wt m) ^ (2 * N + n + 1) :=
          (le_div_iff₀ hpow).mpr hb
        calc ‖d i p.1 m a b‖ ≤ C i / (wt m) ^ (2 * N + n + 1) := h2
          _ = C i * (wt m) ^ (-((2 * N + n + 1 : ℕ) : ℤ)) := by
              rw [div_eq_mul_inv, zpow_neg, zpow_natCast]
      have h2 : ‖iteratedFDerivWithin ℝ (k - i)
            (fun p : ℝ × (Fin n → ℝ) => fourierExp m p.2)
            (Set.Ico (0 : ℝ) τ ×ˢ Set.univ) p‖
          ≤ (2 * Real.pi * (n : ℝ) + 1) ^ k * (wt m) ^ k := by
        have hle := norm_iteratedFDerivWithin_fourierExp_snd_le m _ hS (k - i) p hp
        have hsabs : (∑ i, |((m i : ℤ) : ℝ)|) ≤ (n : ℝ) * wt m := by
          simpa [Fintype.card_fin] using sum_abs_le_card_mul_wt m
        have hx0 : 0 ≤ 2 * Real.pi * ∑ i, |((m i : ℤ) : ℝ)| := by positivity
        have hxle : 2 * Real.pi * ∑ i, |((m i : ℤ) : ℝ)| ≤ 2 * Real.pi * ((n : ℝ) * wt m) :=
          mul_le_mul_of_nonneg_left hsabs (by positivity)
        have hy0 : 0 ≤ 2 * Real.pi * ((n : ℝ) * wt m) := by positivity
        have hstep2 : (2 * Real.pi * ((n : ℝ) * wt m) + 1) ^ k
            ≤ ((2 * Real.pi * (n : ℝ) + 1) * wt m) ^ k := by
          have hbase : 2 * Real.pi * ((n : ℝ) * wt m) + 1
              ≤ (2 * Real.pi * (n : ℝ) + 1) * wt m := by
            have hre : (2 * Real.pi * (n : ℝ) + 1) * wt m
                = 2 * Real.pi * ((n : ℝ) * wt m) + wt m := by ring
            linarith
          exact pow_le_pow_left₀ (by positivity) hbase k
        calc ‖iteratedFDerivWithin ℝ (k - i)
              (fun p : ℝ × (Fin n → ℝ) => fourierExp m p.2)
              (Set.Ico (0 : ℝ) τ ×ˢ Set.univ) p‖
            ≤ (2 * Real.pi * ∑ i, |((m i : ℤ) : ℝ)|) ^ (k - i) := hle
          _ ≤ (2 * Real.pi * ((n : ℝ) * wt m)) ^ (k - i) :=
              pow_le_pow_left₀ hx0 hxle (k - i)
          _ ≤ (2 * Real.pi * ((n : ℝ) * wt m) + 1) ^ (k - i) :=
              pow_le_pow_left₀ hy0 (by linarith) (k - i)
          _ ≤ (2 * Real.pi * ((n : ℝ) * wt m) + 1) ^ k :=
              pow_le_pow_right₀ (by linarith) (Nat.sub_le k i)
          _ ≤ ((2 * Real.pi * (n : ℝ) + 1) * wt m) ^ k := hstep2
          _ = (2 * Real.pi * (n : ℝ) + 1) ^ k * (wt m) ^ k := mul_pow _ _ _
      have h1' : (k.choose i : ℝ) *
            ‖iteratedFDerivWithin ℝ i (fun p : ℝ × (Fin n → ℝ) => d 0 p.1 m a b)
              (Set.Ico (0 : ℝ) τ ×ˢ Set.univ) p‖
          ≤ (k.choose i : ℝ) * (C i * (wt m) ^ (-((2 * N + n + 1 : ℕ) : ℤ))) :=
        mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
      have htop : 0 ≤ (k.choose i : ℝ) * (C i * (wt m) ^ (-((2 * N + n + 1 : ℕ) : ℤ))) :=
        mul_nonneg (Nat.cast_nonneg _)
          (mul_nonneg (hCnn i) (zpow_nonneg hw0.le _))
      have hkey : (k.choose i : ℝ) *
            ‖iteratedFDerivWithin ℝ i (fun p : ℝ × (Fin n → ℝ) => d 0 p.1 m a b)
              (Set.Ico (0 : ℝ) τ ×ˢ Set.univ) p‖ *
          ‖iteratedFDerivWithin ℝ (k - i) (fun p : ℝ × (Fin n → ℝ) => fourierExp m p.2)
              (Set.Ico (0 : ℝ) τ ×ˢ Set.univ) p‖
          ≤ ((k.choose i : ℝ) * (C i * (wt m) ^ (-((2 * N + n + 1 : ℕ) : ℤ)))) *
              ((2 * Real.pi * (n : ℝ) + 1) ^ k * (wt m) ^ k) :=
        mul_le_mul h1' h2 (norm_nonneg _) htop
      refine hkey.trans (le_of_eq ?_)
      rw [← zpow_natCast (wt m) k]
      rw [show ((k.choose i : ℝ) * (C i * (wt m) ^ (-((2 * N + n + 1 : ℕ) : ℤ)))) *
            ((2 * Real.pi * (n : ℝ) + 1) ^ k * (wt m) ^ (k : ℤ))
          = (k.choose i : ℝ) * C i * (2 * Real.pi * (n : ℝ) + 1) ^ k *
            ((wt m) ^ (-((2 * N + n + 1 : ℕ) : ℤ)) * (wt m) ^ (k : ℤ)) by ring]
      rw [← zpow_add₀ (ne_of_gt hw0)]
      rw [show -(((2 * N + n + 1 : ℕ) : ℤ)) + (k : ℤ)
          = (k : ℤ) - ((2 * N + n + 1 : ℕ) : ℤ) from by ring]
    refine hmul.trans ?_
    calc ∑ i ∈ Finset.range (k + 1),
          (k.choose i : ℝ) *
            ‖iteratedFDerivWithin ℝ i (fun p : ℝ × (Fin n → ℝ) => d 0 p.1 m a b)
              (Set.Ico (0 : ℝ) τ ×ˢ Set.univ) p‖ *
            ‖iteratedFDerivWithin ℝ (k - i) (fun p : ℝ × (Fin n → ℝ) => fourierExp m p.2)
              (Set.Ico (0 : ℝ) τ ×ˢ Set.univ) p‖
        ≤ ∑ i ∈ Finset.range (k + 1),
            (k.choose i : ℝ) * C i * (2 * Real.pi * (n : ℝ) + 1) ^ k *
              (wt m) ^ ((k : ℤ) - ((2 * N + n + 1 : ℕ) : ℤ)) :=
          Finset.sum_le_sum hterm
      _ = majConst C n k * (wt m) ^ ((k : ℤ) - ((2 * N + n + 1 : ℕ) : ℤ)) := by
          simp only [majConst]
          rw [Finset.sum_mul]
      _ ≤ majConst C n k * (wt m) ^ (-((n + 1 : ℕ) : ℤ)) :=
          mul_le_mul_of_nonneg_left
            (zpow_le_zpow_right₀ hw1 (by omega : (k : ℤ) - ((2 * N + n + 1 : ℕ) : ℤ)
              ≤ -(((n + 1 : ℕ) : ℤ)))) (hAnn k)
      _ = majFun C n k m := rfl
  have hft := Work.Diff.EXT.hasFTaylorSeriesUpToOn_tsum_gen
    (s := Set.Ico (0 : ℝ) τ ×ˢ Set.univ)
    (ι := Fin n → ℤ) (convex_slab τ) (interior_slab_nonempty (n := n) τ hτ)
    (f := fun m p => d 0 p.1 m a b * fourierExp m p.2) (v := fun k m => majFun C n k m) hf
    (fun k hk => hv k hk)
    (fun k m hk p hp => hbnd k hk m p hp)
  refine (hft.congr ?_).contDiffOn
  intro p hp
  rw [seriesFunM_apply]
  rfl

theorem contDiffOn_series_tower {n : ℕ} (τ : ℝ) (hτ : 0 < τ)
    (d : ℕ → ℝ → (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n)
    (hd : ∀ j M, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico (0 : ℝ) τ, ∀ k : Fin n → ℤ, ∀ a b : Fin n,
      ‖d j t k a b‖ * (Work.Diff.STE.wt k) ^ M ≤ C)
    (ht : ∀ j, ∀ t ∈ Set.Ico (0 : ℝ) τ, ∀ k : Fin n → ℤ, ∀ a b : Fin n,
      HasDerivWithinAt (fun s : ℝ => d j s k a b) (d (j + 1) t k a b) (Set.Ico (0 : ℝ) τ) t) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × (Fin n → ℝ) => Work.Diff.STE.Flat.seriesFunM (d 0 p.1) p.2)
      (Set.Ico (0 : ℝ) τ ×ˢ Set.univ) := by
  rw [contDiffOn_iff_forall_nat_le]
  intro N hN
  rw [contDiffOn_pi]
  intro a
  rw [contDiffOn_pi]
  intro b
  exact contDiffOn_series_component τ hτ d hd ht a b N

end

end Work.Diff.STE.flat
