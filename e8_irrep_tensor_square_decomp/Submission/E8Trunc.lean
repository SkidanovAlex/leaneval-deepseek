import Submission.WCFSetup
import Submission.E8Extract
import Submission.E8ConstChar
import Submission.E8Klimyk
import Submission.E8WCFV
import Submission.E8Support
import Submission.E8Ball
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_Kostant_freudenthal

/-!
# The truncation of the Klimyk sum to the certified ball of radius `4`

The Klimyk form of `A_ρ · ch T` evaluated at `Λ i + ρ` is

  `K_i = ∑_{M ∈ W} ε(M) · mfun (Λ i + ρ - M(λ + ρ))`,

a sum over the *whole* Weyl group.  This file proves that every term with
`M ∉ ballSet` (no word of length `≤ 4`) vanishes, so that the sum is the explicit
450-term sum computed in `Submission/E8CharCompute`/`Submission/E8Klimyk`.

The estimate: put `γ = Λ i + ρ - M(λ+ρ)` and `δ = ρ - Mρ`.  Since
`mfun γ ≠ 0 → qZ γ ≤ 10` and

  `qZ γ = qZ Λ + 160 - 2·⟪Λ, Mλ⟫ - 2·htOf(Mλ) + 2·⟪Λ,δ⟫ + 2·htOf δ`

with `⟪Λ,Mλ⟫ ≤ ⟪Λ,λ⟫`, `htOf(Mλ) ≤ htOf λ = 75`, `⟪Λ,δ⟫ ≥ 0` and
`2⟪Λ,λ⟫ ≤ qZ Λ + 10` (checked for the forty `Λ`), we get `qZ δ ≤ qZ γ ≤ 10`.  But
`qZ δ = 2·htOf δ` (`E8_qZ_rho_sub_wact`), whence `htOf(ρ - Mρ) ≤ 5`, i.e.
`e8ht (Mρ) ≥ 615`, and `E8_wact_small_height_length` then forces `M` to have a word of
length `≤ 4`.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

noncomputable section
open scoped BigOperators

namespace Submission.E8Trunc

open Submission.WCFSetup
open Submission.E8Character
open Commons.LinearAlgebra.Matrix.Cartan
open Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo
open Submission.E8Ball
open Submission.VermaWeight

/-! ## Elementary consequences of the cone conditions -/

/-- `mfun γ ≠ 0` forces the squared length `qZ γ` to be one of `0,2,4,6,8,10`. -/
lemma qZ_le_ten {γ : Fin 8 → ℤ} (h : Submission.E8Numerics.mfun γ ≠ 0) : qZ γ ≤ 10 := by
  have h' : qZ γ = 0 ∨ qZ γ = 2 ∨ qZ γ = 4 ∨ qZ γ = 6 ∨ qZ γ = 8 ∨ qZ γ = 10 :=
    (Submission.E8Support.mfun_ne_zero_iff γ).mp h
  rcases h' with h | h | h | h | h | h <;> rw [h] <;> norm_num

/-- The height is the sum of the `α`-coordinates of `Commons.LinearAlgebra.Matrix.Cartan`. -/
lemma htOf_eq_sum_coords (γ : Fin 8 → ℤ) :
    htOf γ = ∑ i, Commons.LinearAlgebra.Matrix.Cartan.coords γ i :=
  rfl

/-- `posCon` in terms of the `α`-coordinates of `Commons.LinearAlgebra.Matrix.Cartan`. -/
lemma posCon_iff (γ : Fin 8 → ℤ) :
    posCon γ ↔ ∀ i, 0 ≤ Commons.LinearAlgebra.Matrix.Cartan.coords γ i :=
  Iff.rfl

/-- A weight which lies in the cone together with its negative is zero. -/
lemma eq_zero_of_posCon_neg' {δ : Fin 8 → ℤ}
    (h : ∀ i, 0 ≤ Commons.LinearAlgebra.Matrix.Cartan.coords δ i)
    (h' : ∀ i, 0 ≤ Commons.LinearAlgebra.Matrix.Cartan.coords (-δ) i) : δ = 0 := by
  have hneg : ∀ i, (Commons.LinearAlgebra.Matrix.Cartan.coords (-δ)) i
      = -(Commons.LinearAlgebra.Matrix.Cartan.coords δ i) := fun i => by
    have hh := congrFun (Commons.LinearAlgebra.Matrix.Cartan.coords_neg' δ) i
    simpa using hh
  have h1 : Commons.LinearAlgebra.Matrix.Cartan.coords δ = 0 := by
    funext i
    have h2 := h i
    have h3 : 0 ≤ -(Commons.LinearAlgebra.Matrix.Cartan.coords δ i) := by
      have hh := h' i
      rwa [hneg i] at hh
    exact le_antisymm (neg_nonneg.mp h3) h2
  have h2 : E8Character.coords δ = 0 := by
    rw [← E8ConstChar.coords_eq]
    exact h1
  have := E8Character.mulVec_coords δ
  rw [h2, Matrix.mulVec_zero] at this
  exact this.symm

/-- `qZ (a - b) = qZ a - 2⟪a,b⟫ + qZ b`. -/
lemma qZ_sub (a b : Fin 8 → ℤ) : qZ (a - b) = qZ a - 2 * bil a b + qZ b := by
  rw [sub_eq_add_neg, qZ_add', bil_neg_right, qZ_neg]
  ring

/-- The pairing with a dominant weight is nonnegative on the cone. -/
lemma bil_nonneg_of_coords {Λ δ : Fin 8 → ℤ} (hΛ : ∀ i, 0 ≤ Λ i)
    (hδ : ∀ i, 0 ≤ Commons.LinearAlgebra.Matrix.Cartan.coords δ i) : 0 ≤ bil Λ δ := by
  rw [bil, dotProduct]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hΛ i) (hδ i)

lemma bil_nonneg_of_posCon {Λ δ : Fin 8 → ℤ} (hΛ : ∀ i, 0 ≤ Λ i) (hδ : posCon δ) :
    0 ≤ bil Λ δ :=
  bil_nonneg_of_coords hΛ ((posCon_iff δ).mp hδ)

/-- `⟪v,ρ⟫ = htOf v`. -/
lemma bil_rho_eq_htOf (v : Fin 8 → ℤ) : bil v rhoZ = htOf v :=
  bil_rho' v

/-- The height is nonnegative on the cone. -/
lemma htOf_nonneg_of_coords {δ : Fin 8 → ℤ}
    (h : ∀ i, 0 ≤ Commons.LinearAlgebra.Matrix.Cartan.coords δ i) : 0 ≤ htOf δ := by
  rw [htOf_eq_sum_coords]
  exact Finset.sum_nonneg fun i _ => h i

/-- The height decreases along `x - y` in the cone. -/
lemma htOf_le_of_coords_sub {x y : Fin 8 → ℤ}
    (h : ∀ i, 0 ≤ Commons.LinearAlgebra.Matrix.Cartan.coords (x - y) i) : htOf y ≤ htOf x := by
  have h1 : htOf (x - y) = htOf x - htOf y := htOf_sub x y
  have h2 : 0 ≤ htOf (x - y) := htOf_nonneg_of_coords h
  linarith

/-- The pairing with a dominant weight is monotone on the cone. -/
lemma bil_le_of_coords_sub {Λ x y : Fin 8 → ℤ} (hΛ : ∀ i, 0 ≤ Λ i)
    (h : ∀ i, 0 ≤ Commons.LinearAlgebra.Matrix.Cartan.coords (x - y) i) :
    bil Λ y ≤ bil Λ x := by
  have h1 : bil Λ (x - y) = bil Λ x - bil Λ y := bil_sub_right Λ x y
  have h2 : 0 ≤ bil Λ (x - y) := bil_nonneg_of_coords hΛ h
  linarith

/-! ## The numeric input: `2⟪Λ,λ⟫ ≤ qZ Λ + 10` for the forty dominant weights -/

theorem bil_lam_le : ∀ i : Fin 40,
    2 * bil (Submission.E8Extract.ord40get i) Submission.E8Enum.lam
      ≤ qZ (Submission.E8Extract.ord40get i) + 10 := by decide

lemma htOf_lam : htOf Submission.E8Enum.lam = 75 := by decide

lemma qZ_lam : qZ Submission.E8Enum.lam = 10 := by decide

lemma qZ_rhoZ : qZ (rhoZ : Fin 8 → ℤ) = 620 := by decide

lemma htOf_rhoZ : htOf (rhoZ : Fin 8 → ℤ) = 620 := by decide

lemma qZ_lam_rhoZ : qZ (Submission.E8Enum.lam + rhoZ) = 780 := by decide

/-! ## The main estimate -/

/-- The cone condition `posCon (λ - w·λ)`. -/
lemma posCon_lam_sub_wact (L : List (Fin 8)) :
    ∀ i, 0 ≤ Commons.LinearAlgebra.Matrix.Cartan.coords (Submission.E8Enum.lam - wact L
      Submission.E8Enum.lam) i := by
  intro i
  exact E8_dom_sub_wact_mem_cone L Submission.E8Enum.lam
    (by intro j; fin_cases j <;> decide) i

/-- The cone condition `posCon (ρ - w·ρ)`. -/
lemma posCon_rhoZ_sub_wact (L : List (Fin 8)) :
    ∀ i, 0 ≤ Commons.LinearAlgebra.Matrix.Cartan.coords (rhoZ - wact L rhoZ) i := by
  intro i
  exact E8_dom_sub_wact_mem_cone L rhoZ (by intro j; fin_cases j <;> decide) i

/-- **The main estimate.**  For a dominant weight `Λ` of the forty and any `M` in the Weyl group,
the squared length of `ρ - Mρ` is at most that of `Λ + ρ - M(λ+ρ)`. -/
theorem qZ_rho_sub_ap_le (i : Fin 40) (L : List (Fin 8)) :
    qZ (rhoZ - wact L rhoZ)
      ≤ qZ (Submission.E8Extract.ord40get i + rhoZ - wact L
          (Submission.E8Enum.lam + rhoZ)) := by
  have hΛ : ∀ j, 0 ≤ Submission.E8Extract.ord40get i j := Submission.E8Star.ord40_dom i
  set d : Fin 8 → ℤ := rhoZ - wact L rhoZ with hd
  set w : Fin 8 → ℤ := wact L Submission.E8Enum.lam with hw
  have hQ : wact L rhoZ = rhoZ - d := by rw [hd]; abel
  have hN : wact L (Submission.E8Enum.lam + rhoZ) = w + (rhoZ - d) := by
    rw [wact_add, hw, hQ]
  have hb1 : bil (Submission.E8Extract.ord40get i + rhoZ) w
      = bil (Submission.E8Extract.ord40get i) w + htOf w := by
    rw [bil_add_left, bil_comm' rhoZ w, bil_rho_eq_htOf]
  have hb2a : bil (Submission.E8Extract.ord40get i + rhoZ) rhoZ
      = htOf (Submission.E8Extract.ord40get i) + 620 := by
    rw [bil_add_left, bil_rho_eq_htOf, bil_rho_eq_htOf, htOf_rhoZ]
  have hb2b : bil (Submission.E8Extract.ord40get i + rhoZ) d
      = bil (Submission.E8Extract.ord40get i) d + htOf d := by
    rw [bil_add_left, bil_comm' rhoZ d, bil_rho_eq_htOf]
  have hb2 : bil (Submission.E8Extract.ord40get i + rhoZ) (rhoZ - d)
      = htOf (Submission.E8Extract.ord40get i) + 620 - bil (Submission.E8Extract.ord40get i) d
        - htOf d := by
    rw [bil_sub_right, hb2a, hb2b]
    ring
  have hG : qZ (Submission.E8Extract.ord40get i + rhoZ)
      = qZ (Submission.E8Extract.ord40get i) + 2 * htOf (Submission.E8Extract.ord40get i) + 620 := by
    rw [qZ_add', bil_rho_eq_htOf, qZ_rhoZ]
  have hNq : qZ (w + (rhoZ - d)) = 780 := by
    rw [← hN, qZ_wact, qZ_lam_rhoZ]
  have hkey : qZ (Submission.E8Extract.ord40get i + rhoZ - wact L
        (Submission.E8Enum.lam + rhoZ))
      = qZ (Submission.E8Extract.ord40get i) + 160
        - 2 * bil (Submission.E8Extract.ord40get i) w - 2 * htOf w
        + 2 * bil (Submission.E8Extract.ord40get i) d + 2 * htOf d := by
    have h1 : qZ (Submission.E8Extract.ord40get i + rhoZ - wact L
          (Submission.E8Enum.lam + rhoZ))
        = qZ (Submission.E8Extract.ord40get i + rhoZ)
          - 2 * bil (Submission.E8Extract.ord40get i + rhoZ)
              (wact L (Submission.E8Enum.lam + rhoZ))
          + qZ (wact L (Submission.E8Enum.lam + rhoZ)) := qZ_sub _ _
    rw [h1, hN, hNq, bil_add_right, hb1, hb2, hG]
    ring
  have hd_eq : qZ d = 2 * htOf d := E8_qZ_rho_sub_wact L
  have hw_le : bil (Submission.E8Extract.ord40get i) w ≤ bil (Submission.E8Extract.ord40get i)
      Submission.E8Enum.lam := by
    rw [hw]; exact bil_le_of_coords_sub hΛ (posCon_lam_sub_wact L)
  have hw_ht : htOf w ≤ 75 := by
    rw [hw, ← htOf_lam]
    exact htOf_le_of_coords_sub (posCon_lam_sub_wact L)
  have hd_nn : 0 ≤ bil (Submission.E8Extract.ord40get i) d :=
    bil_nonneg_of_coords hΛ (posCon_rhoZ_sub_wact L)
  have hnum : 0 ≤ qZ (Submission.E8Extract.ord40get i) + 10
      - 2 * bil (Submission.E8Extract.ord40get i) Submission.E8Enum.lam := by
    linarith [bil_lam_le i]
  rw [hkey]
  linarith

/-! ## The truncation of the Klimyk sum to the ball of radius `4` -/

/-- **The truncation.**  For a dominant weight `Λ i` of the forty and a Weyl group element `M`,
the term `mfun (Λ i + ρ - M(λ+ρ))` can only be non-zero when `M` lies in the certified ball of
radius `4`. -/
theorem mem_ballSet_of_mfun_ne_zero (i : Fin 40) {M : Matrix (Fin 8) (Fin 8) ℤ} (hM : M ∈ WG)
    (h : Submission.E8Numerics.mfun
      (Submission.E8Extract.ord40get i + rhoZ - ap M
        (Submission.E8Enum.lam + rhoZ)) ≠ 0) :
    M ∈ ballSet := by
  obtain ⟨L, rfl⟩ := mem_WG.mp hM
  rw [wactMat_ap] at h
  have hle := qZ_rho_sub_ap_le i L
  have hle' : qZ (rhoZ - wact L rhoZ) ≤ qZ (Submission.E8Extract.ord40get i + rhoZ
      - wact L (Submission.E8Enum.lam + rhoZ)) := hle
  have hq : qZ (Submission.E8Extract.ord40get i + rhoZ
      - wact L (Submission.E8Enum.lam + rhoZ)) ≤ 10 := qZ_le_ten h
  have hd10 : qZ (rhoZ - wact L rhoZ) = 2 * htOf (rhoZ - wact L rhoZ) :=
    E8_qZ_rho_sub_wact L
  have hht : htOf (rhoZ - wact L rhoZ) ≤ 5 := by linarith
  have hsub : htOf (rhoZ - wact L rhoZ) = htOf (rhoZ : Fin 8 → ℤ) - htOf (wact L rhoZ) :=
    htOf_sub _ _
  have h620 : htOf (rhoZ : Fin 8 → ℤ) = 620 := htOf_rhoZ
  have he8 : 615 ≤ e8ht (wact L rhoZ) := by
    have ht : 615 ≤ htOf (wact L rhoZ) := by linarith
    exact ht
  obtain ⟨L', hlen, hL'⟩ := E8_wact_small_height_length L he8
  obtain ⟨a, ha⟩ := Submission.E8Ball.wact_mem L' hlen
  refine mem_ballSet.mpr ⟨Submission.E8Ball.e8ball[a], List.get_mem _ _, ?_⟩
  show wactMat (Submission.E8Ball.e8ball[a]).2 = wactMat L
  apply wactMat_eq_of_rho_eq
  have hprop := (Submission.E8Ball.e8ball_prop (Submission.E8Ball.e8ball[a])
    (List.get_mem _ _)).2
  rw [hprop, ha, hL' rhoZ]

/-! ## The Klimyk sum over the whole Weyl group is the certified ball sum -/

/-- `mfun` as a `ℚ`-valued function. -/
def mfunQ : (Fin 8 → ℤ) → ℚ := fun ν => (Submission.E8Numerics.mfun ν : ℚ)

/-- The `mfun`-sum over the certified ball of radius `4`, as a computable integer. -/
def KbZ (L : Fin 8 → ℤ) : ℤ :=
  (e8ball.map (fun p => (-1 : ℤ) ^ p.2.length *
    Submission.E8Support.mnorm (qZ (L + rhoZ - wact p.2
      (Submission.E8Enum.lam + rhoZ))))).sum

/-- `mfun` and `mnorm ∘ qZ` agree, as a sum over the ball. -/
lemma ball_mfun_eq_KbZ (L : Fin 8 → ℤ) :
    (e8ball.map (fun p => (-1 : ℤ) ^ p.2.length * Submission.E8Numerics.mfun
      (L + rhoZ - wact p.2 (Submission.E8Enum.lam + rhoZ)))).sum = KbZ L := by
  rw [KbZ]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  rw [Submission.E8Support.mfun_eq_mnorm]

/-- **The shifted ball-sum identity** (integral form). -/
theorem sum_ballSet_int_eq (x : Fin 8 → ℤ) :
    (∑ M ∈ ballSet, (M.det : ℤ) * Submission.E8Numerics.mfun
        (x - ap M (Submission.E8Enum.lam + rhoZ)))
      = (e8ball.map (fun p => (-1 : ℤ) ^ p.2.length * Submission.E8Numerics.mfun
          (x - wact p.2 (Submission.E8Enum.lam + rhoZ)))).sum := by
  have hNodup : (e8ball.map ballMat).Nodup :=
    (e8ball_nodup.of_map Prod.fst).map_on (fun p hp q hq h => ballMat_injOn hp hq h)
  rw [ballSet,
    List.sum_toFinset (fun M => (M.det : ℤ) * Submission.E8Numerics.mfun
      (x - ap M (Submission.E8Enum.lam + rhoZ))) hNodup, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  simp only [Function.comp_apply, ballMat, wactMat_ap, wactMat_det]


/-- The `ℚ`-valued ball sum is the cast of the integral one. -/
lemma sum_ballSet_cast (x : Fin 8 → ℤ) :
    (∑ M ∈ ballSet, (M.det : ℚ) * mfunQ (x - ap M (Submission.E8Enum.lam + rhoZ)))
      = ((∑ M ∈ ballSet, (M.det : ℤ) * Submission.E8Numerics.mfun
          (x - ap M (Submission.E8Enum.lam + rhoZ)) : ℤ) : ℚ) := by
  have hcast : ∀ M : Matrix (Fin 8) (Fin 8) ℤ,
      (M.det : ℚ) * mfunQ (x - ap M (Submission.E8Enum.lam + rhoZ))
        = (((M.det : ℤ) * Submission.E8Numerics.mfun
            (x - ap M (Submission.E8Enum.lam + rhoZ)) : ℤ) : ℚ) := by
    intro M
    simp only [mfunQ]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun M _ => hcast M)]
  exact (map_sum (Int.castRingHom ℚ) (fun M => (M.det : ℤ) * Submission.E8Numerics.mfun
    (x - ap M (Submission.E8Enum.lam + rhoZ))) ballSet).symm


/-- **The truncation step**: the Weyl sum vanishes outside the ball. -/
theorem sum_WG_eq_sum_ballSet (f : (Fin 8 → ℤ) → ℚ) (x : Fin 8 → ℤ)
    (hvan : ∀ M ∈ WG, M ∉ ballSet → (M.det : ℚ) * f (x - ap M (Submission.E8Enum.lam + rhoZ))
      = 0) :
    (∑ M ∈ WG, (M.det : ℚ) * f (x - ap M (Submission.E8Enum.lam + rhoZ)))
      = ∑ M ∈ ballSet, (M.det : ℚ) * f (x - ap M (Submission.E8Enum.lam + rhoZ)) :=
  (Finset.sum_subset ballSet_sub hvan).symm

/-- **The Klimyk value at the dominant points.**  For the forty dominant weights the Weyl sum of
the character of the tensor square is the explicit ball sum `KbZ`, which is evaluated by the
forty `decide`s of `Submission.E8Num40`. -/
theorem WSum_chT_at (N : Submodule U V) (hvN : v ∉ N)
    (hmax : ∀ N' : Submodule U V, v ∉ N' → N' ≤ N) (i : Fin 40) :
    WSum (fun ν => (Module.finrank ℂ ↥(Submission.E8Tensor.TLwt N ν) : ℚ))
        (Submission.E8Extract.ord40get i + rhoV)
      = ((KbZ (Submission.E8Extract.ord40get i) : ℤ) : ℚ) := by
  rw [Submission.E8Klimyk.WSum_chT N hvN hmax, rhoV_eq]
  change (∑ M ∈ WG, (M.det : ℚ) * mfunQ (Submission.E8Extract.ord40get i + rhoZ - ap M
      (Submission.E8Enum.lam + rhoZ))) = ((KbZ (Submission.E8Extract.ord40get i) : ℤ) : ℚ)
  have hvan : ∀ M ∈ WG, M ∉ ballSet → (M.det : ℚ) *
      mfunQ (Submission.E8Extract.ord40get i + rhoZ - ap M
        (Submission.E8Enum.lam + rhoZ)) = 0 := by
    intro M hM hMB
    have h0 : Submission.E8Numerics.mfun (Submission.E8Extract.ord40get i + rhoZ - ap M
        (Submission.E8Enum.lam + rhoZ)) = 0 := by
      by_contra hc
      exact hMB (mem_ballSet_of_mfun_ne_zero i hM hc)
    show (M.det : ℚ) * ((Submission.E8Numerics.mfun (Submission.E8Extract.ord40get i + rhoZ
      - ap M (Submission.E8Enum.lam + rhoZ)) : ℤ) : ℚ) = 0
    rw [h0]
    simp
  rw [sum_WG_eq_sum_ballSet mfunQ (Submission.E8Extract.ord40get i + rhoZ) hvan]
  rw [sum_ballSet_cast, sum_ballSet_int_eq, ball_mfun_eq_KbZ]

end Submission.E8Trunc
