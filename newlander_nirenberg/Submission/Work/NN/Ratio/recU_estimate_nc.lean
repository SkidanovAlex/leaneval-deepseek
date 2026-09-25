import Mathlib
import Submission.Work.NN.Ratio.Defs
import Submission.Work.NN.Ratio.recU_estimate

noncomputable section

open scoped NNReal ENNReal ContDiff
open Set MeasureTheory

namespace Work.NN.Ratio

/-- The estimate on `G.recU` WITHOUT the closedness hypothesis on `f`: the proof of
`recU_estimate` never uses `IsClosedForm`, so the same argument applies verbatim. -/
theorem recU_estimate_nc {n : ℕ} {α : ℝ} (hα : 0 < α) (hα1 : α < 1) (G : Work.NN.Ratio.Geom n) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : Fin n → (Fin n → ℂ) → ℂ, (∀ j, ContDiff ℝ 1 (f j)) →
      (∑ j, Work.CR.Flat.holderNorm 0 α (f j) (Work.CR.Flat.polydisc 0 (fun _ => G.T))) ≠ ⊤ →
      (∀ z : Fin n → ℂ, (∀ l, ‖z l‖ < G.e) →
        ‖G.recU f z‖ ≤ C * ∑ j, (Work.CR.Flat.holderNorm 0 α (f j)
          (Work.CR.Flat.polydisc 0 (fun _ => G.T))).toReal) ∧
      (∀ x y : Fin n → ℂ, (∀ l, ‖x l‖ < G.e) → (∀ l, ‖y l‖ < G.e) →
        ‖G.recU f x - G.recU f y‖ ≤
          C * (∑ j, (Work.CR.Flat.holderNorm 0 α (f j)
            (Work.CR.Flat.polydisc 0 (fun _ => G.T))).toReal) * ‖x - y‖ ^ α) := by
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · subst h0
    refine ⟨1, one_pos, ?_⟩
    intro f hf1 hS
    refine ⟨?_, ?_⟩
    · intro z hz
      simp [Geom.recU]
    · intro x y hx hy
      simp [Geom.recU]
  · have hb0 : (0 : ℝ) ≤ G.b := le_of_lt (lt_trans G.ha G.hab)
    -- the uniform constant for the products `∂̄χ_j · F`
    obtain ⟨C₀, hC₀pos, hC₀⟩ := cutFbar_mul_bound (n := n) hα hα1
      (χ := G.χ) (b := G.b) (T := G.T) G.hbT (cχ := G.cχ) (cχ' := G.cχ')
      G.hcχ (fun ζ hζ => G.hχbar_out ζ hζ) G.hcχ'
    have hC₀G : ∀ (j : Fin n) {F : (Fin n → ℂ) → ℂ} {A H : ℝ}, 0 ≤ A → 0 ≤ H →
        (∀ z : Fin n → ℂ, z ∈ G.trackSet → ‖F z‖ ≤ A) →
        (∀ x y : Fin n → ℂ, x ∈ G.trackSet → y ∈ G.trackSet →
          ‖F x - F y‖ ≤ H * ‖x - y‖ ^ α) →
        (∀ z : Fin n → ℂ, (∀ l, l ≠ j → ‖z l‖ < G.T) → ‖z j‖ ≤ G.b →
          ‖G.cutFbar j z * F z‖ ≤ C₀ * A) ∧
        (∀ a a' : Fin n → ℂ, (∀ l, l ≠ j → ‖a l‖ < G.T) →
          (∀ l, l ≠ j → ‖a' l‖ < G.T) →
          ‖G.cutFbar j a * F a - G.cutFbar j a' * F a'‖
            ≤ C₀ * (A + H) * ‖a - a'‖ ^ α) := by
      intro j F A H hA hH hFb hHb
      obtain ⟨b1, b2⟩ := hC₀ j (F := F) (A := A) (H := H) hA hH
        (fun z hz => hFb z hz) (fun x y hx hy => hHb x y hx hy)
      exact ⟨fun z hz hzj => b1 z hz hzj, fun a a' ha ha' => b2 a a' ha ha'⟩
    set K : ℝ := max 1 (4 * G.r * C₀) + 1 with hKdef
    have hK1 : 1 ≤ K := by
      rw [hKdef]; linarith [le_max_left (1 : ℝ) (4 * G.r * C₀)]
    have hK4 : 4 * G.r * C₀ ≤ K := by
      rw [hKdef]; linarith [le_max_right (1 : ℝ) (4 * G.r * C₀)]
    have hKnn : (0 : ℝ) ≤ K := le_trans zero_le_one hK1
    have hC₀le : 2 * G.r * C₀ ≤ 4 * G.r * C₀ := by
      nlinarith [mul_nonneg (le_of_lt G.hr0) (le_of_lt hC₀pos)]
    refine ⟨2 * G.r * (n : ℝ) * K ^ n * (1 + 64 * (1 + G.L)) + 1, ?_, ?_⟩
    · have h1 : (0 : ℝ) ≤ 2 * G.r := by linarith [G.hr0]
      have h2 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have h3 : (0 : ℝ) ≤ K ^ n := pow_nonneg hKnn n
      have h4 : (0 : ℝ) ≤ 1 + 64 * (1 + G.L) := by linarith [G.hL0]
      have := mul_nonneg (mul_nonneg (mul_nonneg h1 h2) h3) h4
      linarith
    · intro f hf1 hS
      set S : ℝ := ∑ j, (Work.CR.Flat.holderNorm 0 α (f j)
        (Work.CR.Flat.polydisc 0 (fun _ => G.T))).toReal with hSdef
      have hS0 : (0 : ℝ) ≤ S := by
        rw [hSdef]; exact Finset.sum_nonneg (fun i _ => ENNReal.toReal_nonneg)
      have hbase1 : ∀ j (z : Fin n → ℂ), z ∈ G.trackSet → ‖f j z‖ ≤ S := by
        intro j z hz
        have h := norm_le_sum_holderNorm G hS j z hz
        rwa [← hSdef] at h
      have hbase2 : ∀ j (x y : Fin n → ℂ), x ∈ G.trackSet → y ∈ G.trackSet →
          ‖f j x - f j y‖ ≤ S * ‖x - y‖ ^ α := by
        intro j x y hx hy
        have h := norm_sub_le_sum_holderNorm G hα hS j x y hx hy
        rwa [← hSdef] at h
      -- the induction over the stages of the recursion
      have key : ∀ m : ℕ, ∀ k : Fin n,
          (∀ z : Fin n → ℂ, z ∈ G.trackSet → ‖G.recF f m k z‖ ≤ K ^ m * S) ∧
          (∀ x y : Fin n → ℂ, x ∈ G.trackSet → y ∈ G.trackSet →
            ‖G.recF f m k x - G.recF f m k y‖ ≤ K ^ m * S * ‖x - y‖ ^ α) := by
        intro m
        induction m with
        | zero =>
            intro k
            rw [Geom.recF_zero]
            exact ⟨fun z hz => by simpa using hbase1 k z hz,
                   fun x y hx hy => by simpa using hbase2 k x y hx hy⟩
        | succ m ih =>
            intro k
            by_cases hlt : m < n
            · set j : Fin n := ⟨m, hlt⟩ with hjdef
              have hrec : G.recF f (m + 1) k =
                  Work.CR.Flat.Cauchy.dbarTransform G.r j
                    (fun y => G.cutFbar j y * G.recF f m k y) := by
                rw [Geom.recF_succ_of_lt (G := G) hlt]
                rfl
              have hsmk : ContDiff ℝ 1 (G.recF f m k) := contDiff_recF G (k := 0) hf1 m k
              have hcont : Continuous (fun y => G.cutFbar j y * G.recF f m k y) :=
                (((Geom.contDiff_cutFbar (G := G) j).of_le (le_infty 1)).continuous).mul
                  hsmk.continuous
              have hsupp : ∀ y : Fin n → ℂ, G.b ≤ ‖y j‖ →
                  G.cutFbar j y * G.recF f m k y = 0 :=
                fun y hy => by rw [Geom.cutFbar_eq_zero_of_ge (G := G) hy, zero_mul]
              have hA0 : 0 ≤ K ^ m * S := mul_nonneg (pow_nonneg hKnn m) hS0
              have hb1 : ∀ z : Fin n → ℂ, (∀ l, l ≠ j → ‖z l‖ < G.T) → ‖z j‖ ≤ G.b →
                  ‖G.cutFbar j z * G.recF f m k z‖ ≤ C₀ * (K ^ m * S) :=
                (hC₀G j (F := G.recF f m k) (A := K ^ m * S) (H := K ^ m * S) hA0 hA0
                  (fun z hz => (ih k).1 z hz)
                  (fun x y hx hy => (ih k).2 x y hx hy)).1
              have hb2 : ∀ a a' : Fin n → ℂ, (∀ l, l ≠ j → ‖a l‖ < G.T) →
                  (∀ l, l ≠ j → ‖a' l‖ < G.T) →
                  ‖G.cutFbar j a * G.recF f m k a - G.cutFbar j a' * G.recF f m k a'‖
                    ≤ C₀ * (K ^ m * S + K ^ m * S) * ‖a - a'‖ ^ α :=
                (hC₀G j (F := G.recF f m k) (A := K ^ m * S) (H := K ^ m * S) hA0 hA0
                  (fun z hz => (ih k).1 z hz)
                  (fun x y hx hy => (ih k).2 x y hx hy)).2
              constructor
              · intro z hz
                rw [hrec]
                have hfib : ∀ y : Fin n → ℂ, (∀ l, l ≠ j → y l = z l) → ‖y j‖ ≤ G.b →
                    ‖G.cutFbar j y * G.recF f m k y‖ ≤ C₀ * (K ^ m * S) := by
                  intro y hyl hyj
                  exact hb1 y (fun l hl => (Geom.trackSet_update (G := G) hz hyl
                    (lt_of_le_of_lt hyj G.hbT)) l) hyj
                calc ‖Work.CR.Flat.Cauchy.dbarTransform G.r j
                      (fun y => G.cutFbar j y * G.recF f m k y) z‖
                    ≤ 2 * G.r * (C₀ * (K ^ m * S)) :=
                      (Work.CR.Flat.Cauchy.dbarTransform_basic G.hr0 hb0).1 hcont hsupp
                        (C₀ * (K ^ m * S)) z hfib
                  _ ≤ K ^ (m + 1) * S := by
                      have hstep : 2 * G.r * (C₀ * (K ^ m * S)) ≤ K * (K ^ m * S) := by
                        calc 2 * G.r * (C₀ * (K ^ m * S))
                            = (2 * G.r * C₀) * (K ^ m * S) := by ring
                          _ ≤ K * (K ^ m * S) :=
                              mul_le_mul_of_nonneg_right (le_trans hC₀le hK4) hA0
                      calc 2 * G.r * (C₀ * (K ^ m * S)) ≤ K * (K ^ m * S) := hstep
                        _ = K ^ (m + 1) * S := by rw [pow_succ]; ring
              · intro x y hx hy
                rw [hrec]
                have hfib2 : ∀ a a' : Fin n → ℂ, (∀ l, l ≠ j → a l = x l) →
                    (∀ l, l ≠ j → a' l = y l) →
                    ‖G.cutFbar j a * G.recF f m k a - G.cutFbar j a' * G.recF f m k a'‖
                      ≤ (C₀ * (K ^ m * S + K ^ m * S)) * ‖a - a'‖ ^ α := by
                  intro a a' hal ha'l
                  exact hb2 a a' (fun l hl => by rw [hal l hl]; exact hx l)
                    (fun l hl => by rw [ha'l l hl]; exact hy l)
                calc ‖Work.CR.Flat.Cauchy.dbarTransform G.r j
                        (fun y => G.cutFbar j y * G.recF f m k y) x
                      - Work.CR.Flat.Cauchy.dbarTransform G.r j
                        (fun y => G.cutFbar j y * G.recF f m k y) y‖
                    ≤ 2 * G.r * (C₀ * (K ^ m * S + K ^ m * S)) * ‖x - y‖ ^ α :=
                      (Work.CR.Flat.Cauchy.dbarTransform_basic G.hr0 hb0).2.1 hcont hsupp
                        α _ x y hfib2
                  _ ≤ K ^ (m + 1) * S * ‖x - y‖ ^ α := by
                      have hcoef : 2 * G.r * (C₀ * (K ^ m * S + K ^ m * S))
                          ≤ K * (K ^ m * S) := by
                        have h4 := mul_le_mul_of_nonneg_right hK4 hA0
                        nlinarith [h4]
                      calc 2 * G.r * (C₀ * (K ^ m * S + K ^ m * S)) * ‖x - y‖ ^ α
                          ≤ (K * (K ^ m * S)) * ‖x - y‖ ^ α :=
                            mul_le_mul_of_nonneg_right hcoef
                              (Real.rpow_nonneg (norm_nonneg _) α)
                        _ = K ^ (m + 1) * S * ‖x - y‖ ^ α := by rw [pow_succ]; ring
            · have hrec : G.recF f (m + 1) = G.recF f m := by
                rw [Geom.recF_succ (G := G)]
                exact dite_eq_right (not_lt.mpr (not_lt.mp hlt))
              have hmono : K ^ m * S ≤ K ^ (m + 1) * S :=
                mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hK1 (Nat.le_succ m)) hS0
              constructor
              · intro z hz
                rw [hrec]
                exact le_trans ((ih k).1 z hz) hmono
              · intro x y hx hy
                rw [hrec]
                exact le_trans ((ih k).2 x y hx hy)
                  (mul_le_mul_of_nonneg_right hmono (Real.rpow_nonneg (norm_nonneg _) α))
      refine ⟨?_, ?_⟩
      · -- uniform bound
        intro z hz
        have hzt : z ∈ G.trackSet := Geom.solveSet_subset_trackSet (G := G) hz
        have hterm : ∀ j : Fin n,
            ‖Work.CR.Flat.Cauchy.dbarTransform G.r j
              (fun y => G.cutF j y * G.recF f (j : ℕ) j y) z‖ ≤ 2 * G.r * (K ^ n * S) := by
          intro j
          have hm : (j : ℕ) ≤ n := j.isLt.le
          have hsmj : ContDiff ℝ 1 (G.recF f (j : ℕ) j) :=
            contDiff_recF G (k := 0) hf1 (j : ℕ) j
          have hcont : Continuous (fun y => G.cutF j y * G.recF f (j : ℕ) j y) :=
            (((Geom.contDiff_cutF (G := G) j).of_le (le_infty 1)).continuous).mul hsmj.continuous
          have hsupp : ∀ y : Fin n → ℂ, G.b ≤ ‖y j‖ →
              G.cutF j y * G.recF f (j : ℕ) j y = 0 :=
            fun y hy => by rw [Geom.cutF_eq_zero (G := G) hy, zero_mul]
          have hfib : ∀ y : Fin n → ℂ, (∀ l, l ≠ j → y l = z l) → ‖y j‖ ≤ G.b →
              ‖G.cutF j y * G.recF f (j : ℕ) j y‖ ≤ K ^ (j : ℕ) * S := by
            intro y hyl hyj
            have hyt : y ∈ G.trackSet :=
              Geom.trackSet_update (G := G) hzt hyl (lt_of_le_of_lt hyj G.hbT)
            calc ‖G.cutF j y * G.recF f (j : ℕ) j y‖
                = ‖G.cutF j y‖ * ‖G.recF f (j : ℕ) j y‖ := norm_mul _ _
              _ ≤ 1 * (K ^ (j : ℕ) * S) :=
                  mul_le_mul (Geom.norm_cutF_le_one (G := G) j y) ((key (j : ℕ) j).1 y hyt)
                    (norm_nonneg _) zero_le_one
              _ = K ^ (j : ℕ) * S := one_mul _
          have hb := (Work.CR.Flat.Cauchy.dbarTransform_basic G.hr0 hb0).1 hcont hsupp
            (K ^ (j : ℕ) * S) z hfib
          refine le_trans hb ?_
          have hmul : K ^ (j : ℕ) * S ≤ K ^ n * S :=
            mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hK1 hm) hS0
          exact mul_le_mul_of_nonneg_left hmul (by linarith [G.hr0])
        have hmain : ‖G.recU f z‖ ≤
            (2 * G.r * (n : ℝ) * K ^ n * (1 + 64 * (1 + G.L)) + 1) * S := by
          rw [show G.recU f z = ∑ j : Fin n, Work.CR.Flat.Cauchy.dbarTransform G.r j
            (fun y => G.cutF j y * G.recF f (j : ℕ) j y) z from rfl]
          calc ‖∑ j : Fin n, Work.CR.Flat.Cauchy.dbarTransform G.r j
                  (fun y => G.cutF j y * G.recF f (j : ℕ) j y) z‖
              ≤ ∑ j : Fin n, ‖Work.CR.Flat.Cauchy.dbarTransform G.r j
                  (fun y => G.cutF j y * G.recF f (j : ℕ) j y) z‖ := norm_sum_le _ _
            _ ≤ ∑ _j : Fin n, 2 * G.r * (K ^ n * S) :=
                Finset.sum_le_sum (fun j _ => hterm j)
            _ = (n : ℝ) * (2 * G.r * (K ^ n * S)) := by
                rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            _ ≤ (2 * G.r * (n : ℝ) * K ^ n * (1 + 64 * (1 + G.L)) + 1) * S := by
                have hx0 : 0 ≤ 2 * G.r * (n : ℝ) * K ^ n :=
                  mul_nonneg (mul_nonneg (by linarith [G.hr0]) (Nat.cast_nonneg n))
                    (pow_nonneg hKnn n)
                have hprod : 0 ≤ 2 * G.r * (n : ℝ) * K ^ n * (64 * (1 + G.L)) :=
                  mul_nonneg hx0 (by linarith [G.hL0])
                have hx : 2 * G.r * (n : ℝ) * K ^ n ≤
                    2 * G.r * (n : ℝ) * K ^ n * (1 + 64 * (1 + G.L)) + 1 := by
                  nlinarith [hprod]
                calc (n : ℝ) * (2 * G.r * (K ^ n * S))
                    = (2 * G.r * (n : ℝ) * K ^ n) * S := by ring
                  _ ≤ (2 * G.r * (n : ℝ) * K ^ n * (1 + 64 * (1 + G.L)) + 1) * S :=
                      mul_le_mul_of_nonneg_right hx hS0
        rwa [hSdef] at hmain
      · -- Hölder bound
        intro x y hx hy
        have hxt : x ∈ G.trackSet := Geom.solveSet_subset_trackSet (G := G) hx
        have hyt : y ∈ G.trackSet := Geom.solveSet_subset_trackSet (G := G) hy
        have hterm : ∀ j : Fin n,
            ‖Work.CR.Flat.Cauchy.dbarTransform G.r j
              (fun y' => G.cutF j y' * G.recF f (j : ℕ) j y') x
              - Work.CR.Flat.Cauchy.dbarTransform G.r j
              (fun y' => G.cutF j y' * G.recF f (j : ℕ) j y') y‖
              ≤ 2 * G.r * (64 * (1 + G.L) * (K ^ n * S)) * ‖x - y‖ ^ α := by
          intro j
          have hm : (j : ℕ) ≤ n := j.isLt.le
          have hsmj : ContDiff ℝ 1 (G.recF f (j : ℕ) j) :=
            contDiff_recF G (k := 0) hf1 (j : ℕ) j
          have hcont : Continuous (fun y' => G.cutF j y' * G.recF f (j : ℕ) j y') :=
            (((Geom.contDiff_cutF (G := G) j).of_le (le_infty 1)).continuous).mul hsmj.continuous
          have hsupp : ∀ y' : Fin n → ℂ, G.b ≤ ‖y' j‖ →
              G.cutF j y' * G.recF f (j : ℕ) j y' = 0 :=
            fun y' hy' => by rw [Geom.cutF_eq_zero (G := G) hy', zero_mul]
          have hAj0 : 0 ≤ K ^ (j : ℕ) * S := mul_nonneg (pow_nonneg hKnn (j : ℕ)) hS0
          have hfib : ∀ a a' : Fin n → ℂ, (∀ l, l ≠ j → a l = x l) →
              (∀ l, l ≠ j → a' l = y l) →
              ‖G.cutF j a * G.recF f (j : ℕ) j a - G.cutF j a' * G.recF f (j : ℕ) j a'‖
                ≤ (64 * (1 + G.L) * (K ^ (j : ℕ) * S)) * ‖a - a'‖ ^ α := by
            intro a a' hal ha'l
            exact cutF_mul_fiber_holder (n := n) hα hα1 (χ := G.χ) (L := G.L) (b := G.b)
              (T := G.T) G.hbT G.hL0 G.hχ_le (fun ζ hζ => G.hχ_zero ζ hζ) G.hL
              (j := j) (F := G.recF f (j : ℕ) j) (A := K ^ (j : ℕ) * S) hAj0
              (fun z hz => (key (j : ℕ) j).1 z hz)
              (fun z z' hz hz' => (key (j : ℕ) j).2 z z' hz hz')
              a a' (fun l hl => by rw [hal l hl]; exact hxt l)
              (fun l hl => by rw [ha'l l hl]; exact hyt l)
          have hb := (Work.CR.Flat.Cauchy.dbarTransform_basic G.hr0 hb0).2.1 hcont hsupp
            α _ x y hfib
          refine le_trans hb ?_
          have hmul : K ^ (j : ℕ) * S ≤ K ^ n * S :=
            mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hK1 hm) hS0
          have hfac : 0 ≤ 64 * (1 + G.L) := by linarith [G.hL0]
          have hmono : 2 * G.r * (64 * (1 + G.L) * (K ^ (j : ℕ) * S))
              ≤ 2 * G.r * (64 * (1 + G.L) * (K ^ n * S)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmul hfac)
              (by linarith [G.hr0])
          exact mul_le_mul_of_nonneg_right hmono (Real.rpow_nonneg (norm_nonneg _) α)
        have hmain : ‖G.recU f x - G.recU f y‖ ≤
            (2 * G.r * (n : ℝ) * K ^ n * (1 + 64 * (1 + G.L)) + 1) * S * ‖x - y‖ ^ α := by
          rw [show G.recU f x = ∑ j : Fin n, Work.CR.Flat.Cauchy.dbarTransform G.r j
                (fun y' => G.cutF j y' * G.recF f (j : ℕ) j y') x from rfl,
              show G.recU f y = ∑ j : Fin n, Work.CR.Flat.Cauchy.dbarTransform G.r j
                (fun y' => G.cutF j y' * G.recF f (j : ℕ) j y') y from rfl,
              ← Finset.sum_sub_distrib]
          calc ‖∑ j : Fin n, (Work.CR.Flat.Cauchy.dbarTransform G.r j
                  (fun y' => G.cutF j y' * G.recF f (j : ℕ) j y') x
                - Work.CR.Flat.Cauchy.dbarTransform G.r j
                  (fun y' => G.cutF j y' * G.recF f (j : ℕ) j y') y)‖
              ≤ ∑ j : Fin n, ‖Work.CR.Flat.Cauchy.dbarTransform G.r j
                    (fun y' => G.cutF j y' * G.recF f (j : ℕ) j y') x
                  - Work.CR.Flat.Cauchy.dbarTransform G.r j
                    (fun y' => G.cutF j y' * G.recF f (j : ℕ) j y') y‖ :=
                norm_sum_le _ _
            _ ≤ ∑ _j : Fin n, 2 * G.r * (64 * (1 + G.L) * (K ^ n * S)) * ‖x - y‖ ^ α :=
                Finset.sum_le_sum (fun j _ => hterm j)
            _ = (n : ℝ) * (2 * G.r * (64 * (1 + G.L) * (K ^ n * S)) * ‖x - y‖ ^ α) := by
                rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            _ ≤ (2 * G.r * (n : ℝ) * K ^ n * (1 + 64 * (1 + G.L)) + 1) * S
                  * ‖x - y‖ ^ α := by
                have hx0 : 0 ≤ 2 * G.r * (n : ℝ) * K ^ n :=
                  mul_nonneg (mul_nonneg (by linarith [G.hr0]) (Nat.cast_nonneg n))
                    (pow_nonneg hKnn n)
                have hx : (n : ℝ) * 2 * G.r * 64 * (1 + G.L) * K ^ n ≤
                    2 * G.r * (n : ℝ) * K ^ n * (1 + 64 * (1 + G.L)) + 1 := by
                  have hprod : 0 ≤ 2 * G.r * (n : ℝ) * K ^ n * (64 * (1 + G.L)) :=
                    mul_nonneg hx0 (by linarith [G.hL0])
                  nlinarith [hprod]
                calc (n : ℝ) * (2 * G.r * (64 * (1 + G.L) * (K ^ n * S)) * ‖x - y‖ ^ α)
                    = ((n : ℝ) * 2 * G.r * 64 * (1 + G.L) * K ^ n) * S * ‖x - y‖ ^ α := by ring
                  _ ≤ (2 * G.r * (n : ℝ) * K ^ n * (1 + 64 * (1 + G.L)) + 1) * S
                        * ‖x - y‖ ^ α := by
                      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (norm_nonneg _) α)
                      exact mul_le_mul_of_nonneg_right hx hS0
        rwa [hSdef] at hmain


end Work.NN.Ratio
