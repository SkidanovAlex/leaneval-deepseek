import Mathlib
import Submission.Work.Peluse.BoxNormDilation.dilated_directions_ge
import Submission.Work.Peluse.Ulower.boxSumPow_shift_directions
import Submission.Work.Peluse.Ulower.boxSumPow_neg

/-!
# From the sparse arithmetic-progression directions `c[D]` to the dense interval directions `[|c|D]`

For `t >= 2`, `c != 0`, `D >= 1`, a window `symIcc L` and any `F` supported in it, the box-norm
power of Peluse's Definition 2.1 with the **sparse** direction set

`c[D] = {c, 2c, ..., Dc}`

is dominated by the box-norm power with the **dense** direction set

`[|c|D] = {1, 2, ..., |c|D}`,

i.e. there is `C > 0` with `C * ||F||^{2^t}_{box^t_{c[D]}} <= ||F||^{2^t}_{box^t_{[|c|D]}}`.

## Proof

Write `m := |c| >= 1`.

* `c > 0` (so `c = m`) and `m >= 2`: `arithIcc c D = m[D]` is contained in `[mD]`, so the dilation
  comparison `Work.Peluse.BoxNormDilation.dilated_directions_ge` (applied with `c_0 = 1`) gives
  `C * ||F||^{2^t}_{box^t_{m[D]}} <= ||F||^{2^t}_{box^t_{[mD]}}` directly.
* `c < 0`: `||F||^{2^t}_{box^t_{c[D]}} = ||F(-.)||^{2^t}_{box^t_{m[D]}}` (the reflection identity
  `Work.Peluse.Ulower.boxSumPow_neg`), the dilation comparison applies to `F(-.)`, and the interval
  direction set `[mD]` is invariant under reflecting the function (because `[mD]` is a translate of
  its reflection in `0`: `boxSumPow_arithIcc_neg_one_eq`).
* `m = 1`: `c = +-1`, and `arithIcc 1 D` is a translate of `arithIcc (-1) D`, so the two box-norm
  powers coincide.

## Main result

* `Work.Peluse.Ulower.sparse_to_dense`
-/

set_option autoImplicit false

namespace Work.Peluse.Ulower

noncomputable section

open Work.Peluse

/-! ## Membership in the symmetric window -/

lemma mem_symIcc_iff {L : Nat} {x : Int} : x ∈ symIcc L ↔ x.natAbs ≤ L := by
  rw [symIcc, Finset.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    have h3 : |x| ≤ (L : Int) := abs_le.mpr ⟨h1, h2⟩
    have h4 : ((x.natAbs : Nat) : Int) ≤ (L : Int) := by rwa [Int.natCast_natAbs]
    exact_mod_cast h4
  · intro h
    have h3 : ((x.natAbs : Nat) : Int) ≤ (L : Int) := by exact_mod_cast h
    rw [Int.natCast_natAbs] at h3
    exact abs_le.mp h3

/-! ## The interval direction set is a translate of its reflection -/

/-- Translating `arithIcc 1 D` by `-(D+1)` produces the reflected interval `arithIcc (-1) D`. -/
lemma arithIcc_one_image_shift (D : Nat) :
    (arithIcc 1 D).image (fun x : Int => x + (-((D : Int) + 1))) = arithIcc (-1) D := by
  rw [arithIcc, Finset.image_image, arithIcc]
  ext x
  simp only [Finset.mem_image, Finset.mem_Icc, Function.comp_apply, one_mul]
  constructor
  · rintro ⟨n, ⟨hn1, hn2⟩, hn⟩
    refine ⟨D + 1 - n, ⟨by omega, by omega⟩, ?_⟩
    have hcast : ((D + 1 - n : Nat) : Int) = (D : Int) + 1 - (n : Int) := by omega
    rw [hcast]
    omega
  · rintro ⟨m, ⟨hm1, hm2⟩, hm⟩
    refine ⟨D + 1 - m, ⟨by omega, by omega⟩, ?_⟩
    have hcast : ((D + 1 - m : Nat) : Int) = (D : Int) + 1 - (m : Int) := by omega
    rw [hcast]
    omega

/-- The box sum over the reflected interval `arithIcc (-1) D` equals the box sum over the interval
`arithIcc 1 D`, because the two direction sets are translates of each other
(`arithIcc_one_image_shift`) and translating the direction sets does not change the box sum
(`Work.Peluse.Ulower.boxSumPow_shift_directions`). -/
lemma boxSumPow_arithIcc_neg_one_eq (t : Nat) (D : Nat) (S : Finset Int) (G : Int → Complex) :
    boxSumPow t (fun _ : Fin t => arithIcc (-1) D) S G
      = boxSumPow t (fun _ : Fin t => arithIcc 1 D) S G := by
  rw [← arithIcc_one_image_shift D]
  exact boxSumPow_shift_directions t (arithIcc 1 D) S G (-((D : Int) + 1))

/-- The box sum over the *interval* direction set `[D]` is invariant under the reflection
`G ↦ G(-.)` of the function. -/
lemma boxSumPow_arithIcc_one_reflect (t : Nat) (D : Nat) (S : Finset Int) (G : Int → Complex) :
    boxSumPow t (fun _ : Fin t => arithIcc 1 D) S (fun x => G (-x))
      = boxSumPow t (fun _ : Fin t => arithIcc 1 D) S G := by
  rw [← boxSumPow_neg t 1 D S G]
  exact boxSumPow_arithIcc_neg_one_eq t D S G

/-- The norm form of `boxSumPow_arithIcc_neg_one_eq`. -/
lemma boxNormPow_arithIcc_neg_one_eq (t : Nat) (D : Nat) (S : Finset Int) (G : Int → Complex) :
    boxNormPow t (fun _ : Fin t => arithIcc (-1) D) S G
      = boxNormPow t (fun _ : Fin t => arithIcc 1 D) S G :=
  congrArg (fun z : Complex => ‖z‖) (boxSumPow_arithIcc_neg_one_eq t D S G)

/-- The norm form of `boxSumPow_arithIcc_one_reflect`. -/
lemma boxNormPow_arithIcc_one_reflect (t : Nat) (D : Nat) (S : Finset Int) (G : Int → Complex) :
    boxNormPow t (fun _ : Fin t => arithIcc 1 D) S (fun x => G (-x))
      = boxNormPow t (fun _ : Fin t => arithIcc 1 D) S G :=
  congrArg (fun z : Complex => ‖z‖) (boxSumPow_arithIcc_one_reflect t D S G)

/-- For `|c| = 1` the two direction sets `c[D]` and `[D] = arithIcc 1 D` give the same box-norm
power: `c = 1` is the identity, `c = -1` is a translate of `[D]`. -/
lemma boxNormPow_arithIcc_abs_one {t : Nat} {c : Int} (hc : c.natAbs = 1) (D : Nat)
    (S : Finset Int) (f : Int → Complex) :
    boxNormPow t (fun _ : Fin t => arithIcc c D) S f
      = boxNormPow t (fun _ : Fin t => arithIcc 1 D) S f := by
  rcases Int.natAbs_eq_iff.mp hc with h | h
  · rw [h]
    simp
  · rw [h]
    exact boxNormPow_arithIcc_neg_one_eq t D S f

/-! ## The target -/

theorem sparse_to_dense {t : ℕ} (ht : 2 ≤ t) {c : ℤ} (hc : c ≠ 0) {D : ℕ} (hD : 1 ≤ D)
    {L : ℕ} {F : ℤ → ℂ} (hF1 : ∀ x : ℤ, ‖F x‖ ≤ 1)
    (hFspan : ∀ x : ℤ, x ∉ Work.Peluse.symIcc L → F x = 0) :
    ∃ C : ℝ, 0 < C ∧ C * Work.Peluse.boxNormPow t (fun _ : Fin t => Work.Peluse.arithIcc c D)
        (Work.Peluse.symIcc L) F
      ≤ Work.Peluse.boxNormPow t (fun _ : Fin t => Work.Peluse.arithIcc 1 (c.natAbs * D))
        (Work.Peluse.symIcc L) F := by
  have hsupp : SupportIn F L := fun x hx => hFspan x (by
    intro hmem
    rw [mem_symIcc_iff] at hmem
    omega)
  have hm0 : 1 ≤ c.natAbs := Int.natAbs_pos.mpr hc
  rcases eq_or_lt_of_le hm0 with h1 | h2
  · -- `|c| = 1`
    have hm1 : c.natAbs = 1 := h1.symm
    refine ⟨1, one_pos, ?_⟩
    rw [one_mul, boxNormPow_arithIcc_abs_one hm1 D (symIcc L) F, hm1, one_mul]
  · -- `2 <= |c|`
    obtain ⟨C, hC, hP⟩ :=
      Work.Peluse.BoxNormDilation.dilated_directions_ge ht c.natAbs h2
    rcases lt_trichotomy c 0 with hclt | hceq | hcgt
    · -- `c < 0`: reflect the function, then use the interval invariance
      have hneg : (-(((c.natAbs : Nat) : Int))) = c := by
        have hh : ((((-c).natAbs : Nat) : Int)) = -c :=
          Int.natAbs_of_nonneg (by omega)
        rw [Int.natAbs_neg] at hh
        omega
      have hG1 : ∀ x : Int, ‖(fun x : Int => F (-x)) x‖ ≤ 1 := fun x => hF1 (-x)
      have hGsup : SupportIn (fun x : Int => F (-x)) L := by
        intro x hx
        exact hsupp (-x) (by simpa [Int.natAbs_neg] using hx)
      have h := hP 1 D L (fun x : Int => F (-x)) one_ne_zero hD hG1 hGsup
      have hA : boxNormPow t (fun _ : Fin t => arithIcc (((c.natAbs : Nat) : Int) * 1) D)
            (symIcc L) (fun x => F (-x))
          = boxNormPow t (fun _ : Fin t => arithIcc c D) (symIcc L) F := by
        have hb := (boxSumPow_neg t ((c.natAbs : Nat) : Int) D (symIcc L) F).symm
        rw [hneg] at hb
        have hb' : boxSumPow t (fun _ : Fin t => arithIcc (((c.natAbs : Nat) : Int) * 1) D)
              (symIcc L) (fun x => F (-x))
            = boxSumPow t (fun _ : Fin t => arithIcc c D) (symIcc L) F := by
          rw [mul_one]
          exact hb
        exact congrArg (fun z : Complex => ‖z‖) hb'
      have hB : boxNormPow t (fun _ : Fin t => arithIcc 1 (c.natAbs * D)) (symIcc L)
            (fun x => F (-x))
          = boxNormPow t (fun _ : Fin t => arithIcc 1 (c.natAbs * D)) (symIcc L) F :=
        boxNormPow_arithIcc_one_reflect t (c.natAbs * D) (symIcc L) F
      rw [hA, hB] at h
      exact ⟨C, hC, h⟩
    · exact absurd hceq hc
    · -- `c > 0`: `arithIcc c D = arithIcc |c| D`, contained in `arithIcc 1 (|c| D)`
      have hpos : (((c.natAbs : Nat) : Int)) = c := Int.natAbs_of_nonneg hcgt.le
      have h := hP 1 D L F one_ne_zero hD hF1 hsupp
      have hA : boxNormPow t (fun _ : Fin t => arithIcc (((c.natAbs : Nat) : Int) * 1) D)
            (symIcc L) F
          = boxNormPow t (fun _ : Fin t => arithIcc c D) (symIcc L) F := by
        rw [mul_one, hpos]
      rw [hA] at h
      exact ⟨C, hC, h⟩

end

end Work.Peluse.Ulower
