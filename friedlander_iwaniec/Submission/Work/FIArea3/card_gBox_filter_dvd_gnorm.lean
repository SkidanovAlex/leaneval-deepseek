/-
# `Submission.Work.FIArea3.card_gBox_dvd_gnorm` — the `|z|²`-congruence count in the box

For a modulus `d ≥ 1` and a radius `R`, the box `gBox R` contains at most
`ρ(d)·(2R/d + 2)²` Gaussian integers with `d ∣ |z|²`, where
`ρ(d) = #{(a,b) ∈ (ℤ/d)² : a² + b² ≡ 0}` is the number of solutions of the congruence.

This is the `|z|²`-analogue of `FIArea7.card_gBox_filter_dvd_absDelta` (the `Δ`-count) and the
basic input of any *average* statement about `τ(|z|²)` over a lattice region: it turns
`τ(|z|²) = Σ_{d | |z|²} 1` into a sum over the moduli `d`, where the lattice-point count is
elementary.  The argument is separation of variables:

* the *class* of `z` is `(z.re, z.im)` modulo `d`; only the `ρ(d)` classes with
  `a² + b² ≡ 0 (mod d)` are hit (here `d ∣ |z|² = z.re² + z.im²` is used);
* each class meets the box in at most `(2R/d + 1)²` points, because the real parts in one class
  lie in `[-R,R]` and are pairwise congruent modulo `d` (and similarly for the imaginary parts) —
  `Commons.NumberTheory.Int.card_le_of_modEq_abs_le`.
-/
import Mathlib
import Submission.Work.FIArea3.BoxDefs
import Submission.Work.FIArea7.card_gBox_filter_dvd_absDelta
import Submission.Commons.NumberTheory.Int.ncard_int_residue_class_sq_le
import Submission.Commons.NumberTheory.Diophantine.lattice_disk_count_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea3

open Finset Work.FIPlan
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-- `d ∣ |z|²` is the vanishing of `z.re² + z.im²` in `ZMod d`. -/
private lemma dvd_gnorm_iff (d : ℕ) (z : GaussianInt) :
    d ∣ Work.FIPlan.gnorm z ↔ ((z.re : ZMod d) ^ 2 + (z.im : ZMod d) ^ 2 = 0) := by
  have hnorm : z.norm = z.re ^ 2 + z.im ^ 2 := by
    rw [Zsqrtd.norm]; ring
  have hnn : (0 : ℤ) ≤ z.re ^ 2 + z.im ^ 2 := by positivity
  have hgnorm : ((Work.FIPlan.gnorm z : ℕ) : ℤ) = z.re ^ 2 + z.im ^ 2 := by
    rw [Work.FIPlan.gnorm, hnorm]
    exact Int.natAbs_of_nonneg hnn
  have key : (((z.re ^ 2 + z.im ^ 2 : ℤ)) : ZMod d)
      = ((z.re : ZMod d) ^ 2 + (z.im : ZMod d) ^ 2) := by
    push_cast; ring
  rw [← Int.ofNat_dvd, hgnorm, ← key]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd (z.re ^ 2 + z.im ^ 2) d).symm

/-- **The `|z|²`-congruence count in the box.** -/
theorem card_gBox_filter_dvd_gnorm (R : ℤ) (d : ℕ) (hd : 1 ≤ d) :
    (((Work.FIPlan.gBox R).filter (fun z => d ∣ Work.FIPlan.gnorm z)).card : ℝ)
      ≤ (({v : ZMod d × ZMod d | v.1 ^ 2 + v.2 ^ 2 = 0}).ncard : ℝ)
          * (2 * (R : ℝ) / (d : ℝ) + 2) ^ 2 := by
  classical
  haveI : NeZero d := ⟨by omega⟩
  set S : Finset GaussianInt :=
    (Work.FIPlan.gBox R).filter (fun z => d ∣ Work.FIPlan.gnorm z) with hS
  set cl : GaussianInt → ZMod d × ZMod d := fun z => ((z.re : ZMod d), (z.im : ZMod d)) with hcl
  set Sol : Finset (ZMod d × ZMod d) :=
    Finset.univ.filter (fun v => v.1 ^ 2 + v.2 ^ 2 = 0) with hSol
  have hSolcard : (({v : ZMod d × ZMod d | v.1 ^ 2 + v.2 ^ 2 = 0}).ncard : ℝ)
      = (Sol.card : ℝ) := by
    have h : ({v : ZMod d × ZMod d | v.1 ^ 2 + v.2 ^ 2 = 0}) = (↑Sol : Set (ZMod d × ZMod d)) := by
      ext v; simp [hSol]
    rw [h, Set.ncard_coe_finset]
  have hρ0 : (0 : ℝ) ≤ (({v : ZMod d × ZMod d | v.1 ^ 2 + v.2 ^ 2 = 0}).ncard : ℝ) := by
    positivity
  rcases lt_or_ge R 0 with hRneg | hRnn
  · -- empty box
    have hSempty : S = ∅ := by
      rw [hS]
      exact Finset.not_nonempty_iff_eq_empty.mp (by
        rintro ⟨z, hz⟩
        rw [Finset.mem_filter] at hz
        have h := (Work.FIArea7.mem_gBox_iff).mp hz.1
        linarith [h.1, h.2.1])
    rw [hSempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  · -- the real part is bounded by `R ≥ 0`
    have hR0 : (0 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hRnn
    -- the image lies in `Sol`
    have himg_sub : ∀ v ∈ S.image cl, v ∈ Sol := by
      intro v hv
      rw [Finset.mem_image] at hv
      obtain ⟨z, hz, rfl⟩ := hv
      rw [hS, Finset.mem_filter] at hz
      simp only [hSol, Finset.mem_filter, Finset.mem_univ, true_and, hcl]
      exact (dvd_gnorm_iff d z).mp hz.2
    have himg := Finset.card_le_card himg_sub
    -- the fibre bound
    have hfib : ∀ v ∈ S.image cl,
        ((S.filter (fun z => cl z = v)).card : ℝ) ≤ (2 * (R : ℝ) / (d : ℝ) + 2) ^ 2 := by
      intro v hv
      set F : Finset GaussianInt := S.filter (fun z => cl z = v) with hF
      have hmem : ∀ z ∈ F, z ∈ Work.FIPlan.gBox R ∧ (z.re : ZMod d) = v.1
          ∧ (z.im : ZMod d) = v.2 := by
        intro z hz
        rw [hF, Finset.mem_filter] at hz
        have hzS := hz.1
        rw [hS, Finset.mem_filter] at hzS
        refine ⟨hzS.1, ?_, ?_⟩
        · simpa [hcl] using congrArg Prod.fst hz.2
        · simpa [hcl] using congrArg Prod.snd hz.2
      set Ur : Finset ℤ := F.image (fun z => z.re) with hUr
      have hUrle : (Ur.card : ℝ) ≤ 2 * (R : ℝ) / (d : ℝ) + 1 := by
        refine Commons.NumberTheory.Int.card_le_of_modEq_abs_le hd (r := (v.1.val : ℤ))
          (A := (R : ℝ)) hR0 ?_ ?_
        · intro a ha
          simp only [hUr, Finset.mem_image] at ha
          obtain ⟨z, hz, rfl⟩ := ha
          obtain ⟨-, hre, -⟩ := hmem z hz
          rw [Int.modEq_iff_dvd]
          have h := ZMod.intCast_eq_intCast_iff_dvd_sub (z.re) ((v.1.val : ℤ)) d |>.mp ?_
          · exact h
          · have hval : ((v.1.val : ℤ) : ZMod d) = v.1 := by
              push_cast
              exact ZMod.natCast_zmod_val v.1
            exact hre.trans hval.symm
        · intro a ha
          simp only [hUr, Finset.mem_image] at ha
          obtain ⟨z, hz, rfl⟩ := ha
          obtain ⟨hbox, -, -⟩ := hmem z hz
          have h := (Work.FIArea7.mem_gBox_iff).mp hbox
          rw [abs_le]
          have h1 : -((R : ℤ) : ℝ) ≤ (z.re : ℝ) := by
            have h' : ((-R : ℤ) : ℝ) ≤ (z.re : ℝ) := by exact_mod_cast h.1
            simpa using h'
          have h2 : (z.re : ℝ) ≤ ((R : ℤ) : ℝ) := by exact_mod_cast h.2.1
          constructor <;> linarith
      set Ui : Finset ℤ := F.image (fun z => z.im) with hUi
      have hUile : (Ui.card : ℝ) ≤ 2 * (R : ℝ) / (d : ℝ) + 1 := by
        refine Commons.NumberTheory.Int.card_le_of_modEq_abs_le hd (r := (v.2.val : ℤ))
          (A := (R : ℝ)) hR0 ?_ ?_
        · intro a ha
          simp only [hUi, Finset.mem_image] at ha
          obtain ⟨z, hz, rfl⟩ := ha
          obtain ⟨-, -, him⟩ := hmem z hz
          rw [Int.modEq_iff_dvd]
          have h := ZMod.intCast_eq_intCast_iff_dvd_sub (z.im) ((v.2.val : ℤ)) d |>.mp ?_
          · exact h
          · have hval : ((v.2.val : ℤ) : ZMod d) = v.2 := by
              push_cast
              exact ZMod.natCast_zmod_val v.2
            exact him.trans hval.symm
        · intro a ha
          simp only [hUi, Finset.mem_image] at ha
          obtain ⟨z, hz, rfl⟩ := ha
          obtain ⟨hbox, -, -⟩ := hmem z hz
          have h := (Work.FIArea7.mem_gBox_iff).mp hbox
          rw [abs_le]
          have h1 : -((R : ℤ) : ℝ) ≤ (z.im : ℝ) := by
            have h' : ((-R : ℤ) : ℝ) ≤ (z.im : ℝ) := by exact_mod_cast h.2.2.1
            simpa using h'
          have h2 : (z.im : ℝ) ≤ ((R : ℤ) : ℝ) := by exact_mod_cast h.2.2.2
          constructor <;> linarith
      have hinj : F.card ≤ Ur.card * Ui.card := by
        have h1 : F.card ≤ (F.image (fun z => (z.re, z.im))).card := by
          rw [Finset.card_image_of_injOn]
          intro x _ y _ hxy
          exact Zsqrtd.ext (by simpa using congrArg Prod.fst hxy)
                (by simpa using congrArg Prod.snd hxy)
        refine le_trans h1 ?_
        have h2 : (F.image (fun z => (z.re, z.im))) ⊆ Ur.product Ui := by
          intro p hp
          rw [Finset.mem_image] at hp
          obtain ⟨z, hz, rfl⟩ := hp
          exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hz,
            Finset.mem_image_of_mem _ hz⟩
        calc (F.image (fun z => (z.re, z.im))).card
            ≤ (Ur.product Ui).card := Finset.card_le_card h2
          _ = Ur.card * Ui.card := Finset.card_product _ _
      have hbd0 : (0 : ℝ) ≤ 2 * (R : ℝ) / (d : ℝ) + 1 := by
        have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
        have : (0 : ℝ) ≤ 2 * (R : ℝ) / (d : ℝ) := by positivity
        linarith
      have hcast : (F.card : ℝ) ≤ (Ur.card : ℝ) * (Ui.card : ℝ) := by exact_mod_cast hinj
      have h2 : 2 * (R : ℝ) / (d : ℝ) + 1 ≤ 2 * (R : ℝ) / (d : ℝ) + 2 := by linarith
      have hUr2 : (Ur.card : ℝ) ≤ 2 * (R : ℝ) / (d : ℝ) + 2 := le_trans hUrle h2
      have hUi2 : (Ui.card : ℝ) ≤ 2 * (R : ℝ) / (d : ℝ) + 2 := le_trans hUile h2
      have hprod : (Ur.card : ℝ) * (Ui.card : ℝ)
          ≤ (2 * (R : ℝ) / (d : ℝ) + 2) * (2 * (R : ℝ) / (d : ℝ) + 2) :=
        mul_le_mul hUr2 hUi2 (by positivity) (by positivity)
      rw [pow_two]
      exact le_trans hcast hprod
    -- assemble over the fibres
    have hcard := Finset.card_eq_sum_card_fiberwise (f := cl) (s := S)
      (t := S.image cl) (fun z hz => Finset.mem_image_of_mem _ hz)
    have hsum : (S.card : ℝ) ≤ ((S.image cl).card : ℝ) * (2 * (R : ℝ) / (d : ℝ) + 2) ^ 2 := by
      have h1 : (∑ v ∈ S.image cl, ((S.filter (fun z => cl z = v)).card : ℝ))
          ≤ ∑ _v ∈ S.image cl, (2 * (R : ℝ) / (d : ℝ) + 2) ^ 2 := Finset.sum_le_sum hfib
      rw [Finset.sum_const, nsmul_eq_mul] at h1
      rw [hcard, Nat.cast_sum]
      exact h1
    have hsq0 : (0 : ℝ) ≤ (2 * (R : ℝ) / (d : ℝ) + 2) ^ 2 := by positivity
    calc (S.card : ℝ)
        ≤ ((S.image cl).card : ℝ) * (2 * (R : ℝ) / (d : ℝ) + 2) ^ 2 := hsum
      _ ≤ (Sol.card : ℝ) * (2 * (R : ℝ) / (d : ℝ) + 2) ^ 2 := by
          have : ((S.image cl).card : ℝ) ≤ (Sol.card : ℝ) := by exact_mod_cast himg
          exact mul_le_mul_of_nonneg_right this hsq0
      _ = (({v : ZMod d × ZMod d | v.1 ^ 2 + v.2 ^ 2 = 0}).ncard : ℝ)
            * (2 * (R : ℝ) / (d : ℝ) + 2) ^ 2 := by rw [hSolcard]

end

end Work.FIArea3
