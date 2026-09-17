import Submission.WCFSetup
import Submission.E8CharCompute
import Submission.E8WCFBall
import Submission.E8Support
import Submission.WeylReflect
import Submission.WeylBall
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_qZ_rho_sub_wact
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_rho_sub_wact_rho_eq_sum
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_wact_small_height_length
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_qZ_add_mem_cone_dominant
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_dom_sub_wact_mem_cone
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_qZ_le_of_dominant
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_dominant_conj_unique
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_wact_fixes_strict_dominant

/-!
# The Weyl character formula for `V = L(ω₁+ω₈)` — infrastructure

`Submission/WCFSetup.lean` builds the Weyl group `W(E₈)` as a finite set `WG` of matrices acting on
the weight lattice, the *Weyl sum* `WSum f x = ∑_{M ∈ WG} det(M) · f (x - M ρ)`, proves that it is
anti-invariant when `f` is `W`-invariant, and shows that the sum reduces to the certified
450-element ball `Submission/E8Ball.e8ball` whenever the terms outside the ball vanish.

This file contains the parts of the proof of the **Weyl character formula for `V = L(ω₁+ω₈)`**

  `WSum (ch V) x = ∑_{M ∈ WG} det(M) · [M(λ+ρ) = x]`   (`A_ρ · ch V = A_{λ+ρ}`)

that do not need the numerical ball evaluation:

* `mfun_wact`, `mfun_ap` — the character `ch V = mfun` is `W`-invariant;
* `WSum_mfun_anti` — hence the Weyl sum of `mfun` is anti-invariant;
* `altLP`, `altLP_ap`, `altLP_wact` — the alternant of `λ+ρ` is anti-invariant;
* `hqq_le` — the support estimate `qq (ρ - wρ) ≤ qq (ν + ρ - wρ)` for dominant `ν`.

The remaining steps (the case analysis on the dominant weight `x`, the reduction of the Weyl sum to
the ball of radius `4`, and the seven `decide`-checked values of `Submission/E8CharCompute.lean`)
are recorded in the roadmap section of `Submission.lean`.
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

noncomputable section
open scoped BigOperators

namespace Submission.E8WCFV

open Submission.WCFSetup
open Submission.E8Numerics Submission.E8Support Submission.E8CharCompute
open Submission.WeylReflect
open Commons.LinearAlgebra.Matrix.Cartan
open Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo

/-- **`mfun` is `W`-invariant** (it is `mnorm ∘ qZ` and `qZ` is `W`-invariant). -/
theorem mfun_wact (L : List (Fin 8)) (v : Fin 8 → ℤ) :
    Submission.E8Numerics.mfun (wact L v) = Submission.E8Numerics.mfun v := by
  rw [Submission.E8Support.mfun_eq_mnorm]
  rw [show qq (wact L v) = qq v from qZ_wact L v]
  rw [Submission.E8Support.mfun_eq_mnorm]

/-- **`mfun` is invariant under every element of the finite Weyl group.** -/
theorem mfun_ap (M : Matrix (Fin 8) (Fin 8) ℤ) (hM : M ∈ WG) (v : Fin 8 → ℤ) :
    Submission.E8Numerics.mfun (ap M v) = Submission.E8Numerics.mfun v := by
  obtain ⟨L, rfl⟩ := mem_WG.mp hM
  rw [wactMat_ap, mfun_wact]

/-- **The Weyl sum of `mfun` is anti-invariant.** -/
theorem WSum_mfun_anti (x : Fin 8 → ℤ) (L : List (Fin 8)) :
    WSum (fun v => (Submission.E8Numerics.mfun v : ℚ)) (wact L x)
      = (((-1 : ℤ) ^ L.length : ℤ) : ℚ)
        * WSum (fun v => (Submission.E8Numerics.mfun v : ℚ)) x :=
  WSum_anti (fun M hM y => by
    show ((Submission.E8Numerics.mfun (ap M y) : ℚ)) = ((Submission.E8Numerics.mfun y : ℚ))
    rw [mfun_ap M hM y]) x L

/-- The right-hand side of the Weyl character formula: the alternant of `λ + ρ`. -/
def altLP (x : Fin 8 → ℤ) : ℚ :=
  ∑ M ∈ WG, (M.det : ℚ) * (if ap M (Submission.E8Enum.lam + rhoV) = x then 1 else 0)

/-- `ap` commutes with matrix multiplication. -/
theorem ap_mul' (M N : Matrix (Fin 8) (Fin 8) ℤ) (v : Fin 8 → ℤ) :
    ap (M * N) v = ap M (ap N v) := ap_mul M N v

/-- **The alternant of `λ+ρ` is anti-invariant.** -/
theorem altLP_ap (x : Fin 8 → ℤ) {M₀ : Matrix (Fin 8) (Fin 8) ℤ} (h₀ : M₀ ∈ WG) :
    altLP (ap M₀ x) = (M₀.det : ℚ) * altLP x := by
  classical
  obtain ⟨M₀', hM₀', h₁, h₂⟩ := WG_inv h₀
  have hinj : ∀ a b : Fin 8 → ℤ, ap M₀ a = ap M₀ b → a = b := by
    intro a b hab
    have := congrArg (ap M₀') hab
    rwa [← ap_mul, h₂, ap_one, ← ap_mul, h₂, ap_one] at this
  rw [altLP, altLP, Finset.mul_sum]
  have hbij : (∑ M ∈ WG, (M.det : ℚ) * (if ap M (Submission.E8Enum.lam + rhoV) = ap M₀ x
        then 1 else 0))
      = ∑ N ∈ WG, ((M₀ * N).det : ℚ)
          * (if ap (M₀ * N) (Submission.E8Enum.lam + rhoV) = ap M₀ x then 1 else 0) := by
    refine (Finset.sum_bij (fun N _ => M₀ * N) ?_ ?_ ?_ ?_).symm
    · intro N hN; exact WG_mul h₀ hN
    · intro N₁ h₁' N₂ h₂' heq
      have := congrArg (fun P : Matrix (Fin 8) (Fin 8) ℤ => M₀' * P) heq
      simpa only [← Matrix.mul_assoc, h₂, Matrix.one_mul] using this
    · intro M hM
      exact ⟨M₀' * M, WG_mul hM₀' hM, by rw [← Matrix.mul_assoc, h₁, Matrix.one_mul]⟩
    · intro N hN; rfl
  rw [hbij]
  refine Finset.sum_congr rfl fun N hN => ?_
  rw [Matrix.det_mul, ap_mul']
  by_cases h : ap N (Submission.E8Enum.lam + rhoV) = x
  · rw [if_pos h, if_pos (by rw [h])]
    push_cast; ring
  · rw [if_neg h, if_neg (fun hh => h (hinj _ _ hh))]
    ring

/-- **The alternant of `λ+ρ`, in word form.** -/
theorem altLP_wact (x : Fin 8 → ℤ) (L : List (Fin 8)) :
    altLP (wact L x) = (((-1 : ℤ) ^ L.length : ℤ) : ℚ) * altLP x := by
  rw [← wactMat_ap, altLP_ap x (wactMat_mem L), wactMat_det]

/-- **Support estimate.**  For a dominant weight `ν` and a positive sum of roots `δ`, the squared
length of `ν + δ` is at least that of `δ`.  This is the estimate that confines the Weyl sum of
`ch V` to the ball of radius `4`. -/
theorem hqq_le (ν δ : Fin 8 → ℤ) (hν : ∀ i, 0 ≤ ν i)
    (hδ : ∀ i, 0 ≤ Commons.LinearAlgebra.Matrix.Cartan.coords δ i) :
    qZ δ ≤ qZ (ν + δ) := by
  have h := Commons.LinearAlgebra.Matrix.Cartan.E8_qZ_add_mem_cone_dominant ν δ hν hδ
  have h0 : 0 ≤ qZ ν := by
    have hd := diag_le_qZ ν hν
    have hterm : ∀ i : Fin 8, (0 : ℤ) ≤ E8inv i i * (ν i)^2 := by
      intro i
      exact mul_nonneg (by fin_cases i <;> decide) (sq_nonneg _)
    have hsum0 : 0 ≤ ∑ i, E8inv i i * (ν i)^2 := Finset.sum_nonneg (fun i _ => hterm i)
    linarith
  linarith


section Support

/-- **`mfun` vanishes of the support `qq ≤ 10`.** -/
theorem mfun_eq_zero_of_ten_lt (v : Fin 8 → ℤ) (h : 10 < qq v) :
    Submission.E8Numerics.mfun v = 0 := by
  by_contra h0
  have hmem := (Submission.E8Support.mfun_ne_zero_iff v).mp h0
  rcases hmem with h' | h' | h' | h' | h' | h' <;> omega

end Support


/-! ## Dominant weights: the two vanishing regions -/

/-- **The support estimate in the form used below**: for a dominant `ν` and a cone element `δ`,
`qq ν ≤ qq (ν + δ)`. -/
theorem qq_le_add (ν δ : Fin 8 → ℤ) (hν : ∀ i, 0 ≤ ν i)
    (hδ : ∀ i, 0 ≤ Commons.LinearAlgebra.Matrix.Cartan.coords δ i) :
    qq ν ≤ qq (ν + δ) := by
  refine Commons.LinearAlgebra.Matrix.Cartan.E8_qZ_le_of_dominant ν (ν + δ) hν (fun i => ?_)
  rw [show Commons.LinearAlgebra.Matrix.Cartan.coords ((ν + δ) - ν) i
      = Commons.LinearAlgebra.Matrix.Cartan.coords δ i from by
    congr 1; abel]
  exact hδ i

/-- `λ + ρ = (2,1,1,1,1,1,1,2)` is strictly dominant. -/
theorem lambda_rho_strict : ∀ i : Fin 8, 1 ≤ (Submission.E8Enum.lam + rhoV) i := by
  intro i; fin_cases i <;> decide

/-- `ap M ρ` is `wρ` for the word `L` with `M = wactMat L`. -/
lemma ap_rhoV_eq (L : List (Fin 8)) : ap (wactMat L) rhoV = wact L rhoZ := by
  rw [wactMat_ap, rhoV_eq]

/-- `coords (ρ - wρ)` is nonnegative, in word form. -/
lemma coords_rhoV_sub_wact_nonneg (L : List (Fin 8)) (i : Fin 8) :
    0 ≤ Commons.LinearAlgebra.Matrix.Cartan.coords (rhoV - wact L rhoZ) i := by
  rw [← rhoV_eq]
  have hx : ∀ i : Fin 8, (0 : ℤ) ≤ rhoZ i := by decide
  exact E8_dom_sub_wact_mem_cone L rhoZ hx i

/-- `coords (ρ - wρ)` is nonnegative. -/
lemma coords_rhoV_sub_ap_nonneg (M : Matrix (Fin 8) (Fin 8) ℤ) (hM : M ∈ WG)
    (i : Fin 8) :
    0 ≤ Commons.LinearAlgebra.Matrix.Cartan.coords (rhoV - ap M rhoV) i := by
  obtain ⟨L, rfl⟩ := mem_WG.mp hM
  rw [ap_rhoV_eq]
  exact coords_rhoV_sub_wact_nonneg L i

/-- **`altLP` vanishes off the orbit of `λ+ρ`.** -/
theorem altLP_eq_zero_of_forall_ne (x : Fin 8 → ℤ)
    (h : ∀ L : List (Fin 8), wact L (Submission.E8Enum.lam + rhoV) ≠ x) : altLP x = 0 := by
  rw [altLP]
  refine Finset.sum_eq_zero fun M hM => ?_
  obtain ⟨L, rfl⟩ := mem_WG.mp hM
  rw [if_neg, mul_zero]
  intro hcon
  rw [ap_mulVec, wactMat_mulVec] at hcon
  exact h L hcon

/-- **`altLP` at `λ+ρ`**: the only Weyl group element fixing the strictly dominant weight `λ+ρ`
is the identity. -/
theorem altLP_lambda_rho : altLP (Submission.E8Enum.lam + rhoV) = 1 := by
  classical
  rw [altLP]
  rw [Finset.sum_eq_single (1 : Matrix (Fin 8) (Fin 8) ℤ)]
  · rw [if_pos (ap_one _), Matrix.det_one]; norm_num
  · intro M hM hMne
    rw [if_neg, mul_zero]
    intro hcon
    apply hMne
    obtain ⟨L, rfl⟩ := mem_WG.mp hM
    have hfix : wact L (Submission.E8Enum.lam + rhoV) = Submission.E8Enum.lam + rhoV := by
      rw [ap_mulVec, wactMat_mulVec] at hcon
      exact hcon
    have hfixall := E8_wact_fixes_strict_dominant lambda_rho_strict hfix
    have h1 : wact L rhoZ = rhoZ := hfixall rhoZ
    have : wactMat L = wactMat ([] : List (Fin 8)) := wactMat_eq_of_rho_eq h1
    rw [this, wactMat_nil]
  · intro h1
    exact absurd WG_one h1

/-- **`altLP` vanishes on the walls of the dominant chamber.** -/
theorem altLP_eq_zero_of_wall (x : Fin 8 → ℤ) (i : Fin 8) (hi : x i = 0) : altLP x = 0 := by
  have hfix : wact [i] x = x := by
    show Commons.LinearAlgebra.Matrix.Cartan.sref i x = x
    funext j
    simp [Commons.LinearAlgebra.Matrix.Cartan.sref, hi]
  have h := altLP_wact x [i]
  rw [hfix] at h
  simp at h
  linarith

/-- **The Weyl sum of `mfun` vanishes on the walls of the dominant chamber.** -/
theorem WSum_mfun_eq_zero_of_wall (x : Fin 8 → ℤ) (i : Fin 8) (hi : x i = 0) :
    WSum (fun v => (Submission.E8Numerics.mfun v : ℚ)) x = 0 := by
  have hfix : wact [i] x = x := by
    show Commons.LinearAlgebra.Matrix.Cartan.sref i x = x
    funext j
    simp [Commons.LinearAlgebra.Matrix.Cartan.sref, hi]
  have h := WSum_mfun_anti x [i]
  rw [hfix] at h
  simp at h
  linarith

/-- **The Weyl sum of `mfun` vanishes above the support radius.** -/
theorem WSum_mfun_eq_zero_of_gt (x : Fin 8 → ℤ) (hν : ∀ i, 0 ≤ (x - rhoV) i)
    (h : 10 < qq (x - rhoV)) :
    WSum (fun v => (Submission.E8Numerics.mfun v : ℚ)) x = 0 := by
  rw [WSum]
  refine Finset.sum_eq_zero fun M hM => ?_
  have hzero : Submission.E8Numerics.mfun (x - ap M rhoV) = 0 := by
    apply mfun_eq_zero_of_ten_lt
    have hsplit : x - ap M rhoV = (x - rhoV) + (rhoV - ap M rhoV) := by abel
    rw [hsplit]
    refine lt_of_lt_of_le h (qq_le_add (x - rhoV) (rhoV - ap M rhoV) hν ?_)
    exact coords_rhoV_sub_ap_nonneg M hM
  rw [hzero]
  simp

/-- Casting a `ℤ`-valued list sum to `ℚ`. -/
lemma sum_map_cast {α : Type*} (l : List α) (f : α → ℤ) :
    (l.map (fun x => (f x : ℚ))).sum = ((l.map f).sum : ℚ) := by
  induction l with
  | nil => simp
  | cons a t ih =>
      rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, ih]
      push_cast; ring

/-- **The ball computation.**  For a strictly dominant `x` with `qq (x-ρ) ≤ 10` the Weyl sum of
`ch V` reduces to the certified ball of radius `4` and takes the value `[x = λ+ρ]`. -/
theorem WSum_mfun_eq_of_le (x : Fin 8 → ℤ) (hx : ∀ i, 1 ≤ x i)
    (hqq : qq (x - rhoV) ≤ 10) :
    WSum (fun v => (Submission.E8Numerics.mfun v : ℚ)) x
      = (if x = Submission.E8Enum.lam + rhoV then 1 else 0) := by
  have hx0 : ∀ i, 0 ≤ (x - rhoV) i := fun i => by have := hx i; simp [rhoV]; omega
  -- the terms outside the ball vanish
  have hvan : ∀ M ∈ WG, M ∉ ballSet →
      (M.det : ℚ) * ((fun v => (Submission.E8Numerics.mfun v : ℚ)) (x - ap M rhoV)) = 0 := by
    intro M hM hMB
    have hmf : Submission.E8Numerics.mfun (x - ap M rhoV) = 0 := by
      by_contra hne
      have hle : qq (x - ap M rhoV) ≤ 10 := by
        have hmem := (Submission.E8Support.mfun_ne_zero_iff (x - ap M rhoV)).mp hne
        rcases hmem with h' | h' | h' | h' | h' | h' <;> omega
      -- the ball membership
      obtain ⟨L, rfl⟩ := mem_WG.mp hM
      have hle' : qq (x - wact L rhoZ) ≤ 10 := by rwa [ap_rhoV_eq] at hle
      have hlow : qq (rhoZ - wact L rhoZ) ≤ qq (x - wact L rhoZ) := by
        have hsplit : x - wact L rhoZ = (x - rhoV) + (rhoV - wact L rhoZ) := by
          rw [rhoV_eq]; abel
        rw [hsplit]
        exact hqq_le (x - rhoV) (rhoV - wact L rhoZ) hx0
          (coords_rhoV_sub_wact_nonneg L)
      have h1 : qq (rhoZ - wact L rhoZ) ≤ 10 := le_trans hlow hle'
      have h2 : e8ht (rhoZ - wact L rhoZ) ≤ 5 := by
        rw [show qq (rhoZ - wact L rhoZ)
            = 2 * e8ht (rhoZ - wact L rhoZ) from E8_qZ_rho_sub_wact L] at h1
        omega
      have hht : 615 ≤ e8ht (wact L rhoZ) := by
        rw [e8ht_rhoZ_sub] at h2; omega
      obtain ⟨L', hL'len, hL'⟩ := E8_wact_small_height_length L hht
      obtain ⟨a, ha⟩ := Submission.E8Ball.wact_mem L' hL'len
      refine hMB (mem_ballSet.mpr ⟨Submission.E8Ball.e8ball[a], List.get_mem _ _, ?_⟩)
      show wactMat (Submission.E8Ball.e8ball[a]).2 = wactMat L
      rw [wactMat_eq_of_rho_eq]
      rw [(Submission.E8Ball.e8ball_prop (Submission.E8Ball.e8ball[a]) (List.get_mem _ _)).2, ha]
      exact hL' rhoZ
    change (M.det : ℚ) * ((Submission.E8Numerics.mfun (x - ap M rhoV) : ℚ)) = 0
    rw [hmf]
    simp
  rw [WSum_eq_ballSum' _ _ hvan]
  -- evaluate the ball sum at `ν := x - ρ ∈ the7`
  have hmem : (x - rhoV) ∈ Submission.E8Enum.the7 :=
    Submission.E8Support.mem_the7_of_norm_le (x - rhoV) hx0 hqq
  have hball := Submission.E8WCFBall.ballSum_the7 (x - rhoV) hmem
  have hxv : x = (x - rhoV) + rhoV := by abel
  have hsum : (Submission.E8Ball.e8ball.map (fun p => (-1 : ℚ) ^ p.2.length *
        ((fun v => (Submission.E8Numerics.mfun v : ℚ)) (x - p.1)))).sum
      = ((Submission.E8Ball.e8ball.map (fun p => (-1 : ℤ) ^ p.2.length
        * mnorm (qZ ((x - rhoV) + rhoZ - p.1)))).sum : ℚ) := by
    rw [← sum_map_cast]
    apply congrArg List.sum
    apply List.map_congr_left
    intro p hp
    simp only
    have h1 : (x - p.1 : Fin 8 → ℤ) = (x - rhoV) + rhoZ - p.1 := by
      rw [← rhoV_eq]; abel
    rw [h1, Submission.E8Support.mfun_eq_mnorm]
    push_cast
    ring
  have hball' : (Submission.E8CharCompute.ballSum
        (fun z => mnorm (qZ ((x - rhoV) + rhoZ - z))) : ℚ)
      = ((Submission.E8Ball.e8ball.map (fun p => (-1 : ℤ) ^ p.2.length
        * mnorm (qZ ((x - rhoV) + rhoZ - p.1)))).sum : ℚ) := by
    rw [Submission.E8CharCompute.ballSum]
  rw [hsum, ← hball', hball]
  by_cases h : (x - rhoV) = Submission.E8Enum.lam
  · rw [if_pos h]
    have : x = Submission.E8Enum.lam + rhoV := by rw [← h]; abel
    rw [if_pos this]; norm_num
  · rw [if_neg h]
    have : x ≠ Submission.E8Enum.lam + rhoV := fun hc => h (by
      have := congrArg (fun y => y - rhoV) hc; simpa using this)
    rw [if_neg this]
    norm_num

/-- **`altLP` vanishes off `W(λ+ρ)`**, for a dominant weight. -/
theorem altLP_eq_zero_of_ne (x : Fin 8 → ℤ) (hx : Dominant x)
    (h : x ≠ Submission.E8Enum.lam + rhoV) : altLP x = 0 := by
  refine altLP_eq_zero_of_forall_ne x fun L hcon => h ?_
  have hx' : ∀ i, 0 ≤ (Submission.E8Enum.lam + rhoV) i := by
    intro i; have := lambda_rho_strict i; omega
  have h1 : x = Submission.E8Enum.lam + rhoV :=
    Commons.LinearAlgebra.Matrix.Cartan.E8_dominant_conj_unique hx hx' hcon
      (by rw [wact_nil])
  exact h1

/-- **The Weyl character formula for `V = L(ω₁+ω₈)`**:  `A_ρ · ch V = A_{λ+ρ}`. -/
theorem WCF_V (x : Fin 8 → ℤ) :
    WSum (fun v => (Submission.E8Numerics.mfun v : ℚ)) x = altLP x := by
  obtain ⟨x', ⟨L, hL⟩, hdom⟩ := exists_dominant_WConj x
  -- both sides are anti-invariant, so it suffices to prove the dominant case
  have hLw : wact L x = x' := hL
  have hLHS := WSum_mfun_anti x L
  rw [hLw] at hLHS
  have hRHS := altLP_wact x L
  rw [hLw] at hRHS
  have heps : ((((-1 : ℤ) ^ L.length : ℤ) : ℚ) * ((((-1 : ℤ) ^ L.length : ℤ) : ℚ)) = 1) := by
    push_cast
    rw [← pow_add, show L.length + L.length = L.length * 2 from by ring]
    exact Even.neg_one_pow ⟨L.length, by ring⟩
  have hdomcase : WSum (fun v => (Submission.E8Numerics.mfun v : ℚ)) x' = altLP x' := by
    by_cases hstrict : ∀ i, 1 ≤ x' i
    · by_cases hqq : qq (x' - rhoV) ≤ 10
      · rw [WSum_mfun_eq_of_le x' hstrict hqq]
        by_cases h : x' = Submission.E8Enum.lam + rhoV
        · rw [if_pos h, h, altLP_lambda_rho]
        · rw [if_neg h]
          rw [altLP_eq_zero_of_ne x' hdom h]
      · have hgt : 10 < qq (x' - rhoV) := not_le.mp hqq
        rw [WSum_mfun_eq_zero_of_gt x' (fun i => by
          have h1 := hstrict i
          have h2 : (rhoV : Fin 8 → ℤ) i = 1 := rfl
          simp only [Pi.sub_apply, h2]
          omega) hgt]
        rw [altLP_eq_zero_of_ne x' hdom]
        intro hc
        rw [hc] at hgt
        have : qq (Submission.E8Enum.lam + rhoV - rhoV) = 10 := by
          rw [show Submission.E8Enum.lam + rhoV - rhoV = Submission.E8Enum.lam from by abel]
          decide
        omega
    · rw [not_forall] at hstrict
      obtain ⟨i, hi⟩ := hstrict
      have hzero : x' i = 0 := by have := hdom i; omega
      rw [WSum_mfun_eq_zero_of_wall x' i hzero, altLP_eq_zero_of_wall x' i hzero]
  have key : ((((-1 : ℤ) ^ L.length : ℤ) : ℚ)) * WSum (fun v => (Submission.E8Numerics.mfun v : ℚ)) x
      = ((((-1 : ℤ) ^ L.length : ℤ) : ℚ)) * altLP x := by
    rw [← hLHS, hdomcase, hRHS]
  have := congrArg (fun z : ℚ => ((((-1 : ℤ) ^ L.length : ℤ) : ℚ)) * z) key
  rwa [← mul_assoc, heps, one_mul, ← mul_assoc, heps, one_mul] at this

end Submission.E8WCFV
