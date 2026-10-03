/-
# `Work.FIArea6Hecke.R2.BoxSumKappa`

The box sum of an `M`-periodic function equals `kappa M` times its sum over an arbitrary
complete residue system mod `M`.

Writing `N = gnorm M` for the norm of `M : ℤ[i]`, the box `gbox N = [0,N)²` fibres over the
residue classes mod `M`: the fibre `crsFib M N s = {a ∈ gbox N : M ∣ a - s}` has the same
cardinality `kappa M` for every `s`.  Consequently, for any complete residue system `S` mod `M`
and any function `f` invariant under adding multiples of `M`,

  `boxSum N f = ∑_{a ∈ gbox N} f a = kappa M · ∑_{s ∈ S} f s`.

The proof splits into two independent facts about the fibres:

* `crsFib_card_eq` — all fibres have the same cardinality (proved by an explicit injection
  between two fibres built from the coordinatewise reduction `crsRed`);
* the box is the disjoint union of the fibres over `S` (`IsCRS` gives exactly one `s` per
  class), which turns the box sum into a nested sum.
-/
import Mathlib
import Submission.Work.FIArea6Hecke.R2.Defs
import Submission.Work.FIArea6Hecke.CGD.FibDefs
import Submission.Work.FIArea6Hecke.CGD.CrsCalculus

namespace Work.FIArea6Hecke.R2

open scoped BigOperators
open Work.FIArea6Hecke.CGD
open Work.FIArea6Hecke.R (gbox boxSum IsCRS)

noncomputable section

/-- If two Gaussian integers have the same coordinatewise reduction mod `N`, then they differ by
a multiple of `(N : ℤ[i])`. -/
lemma dvd_of_crsRed_eq {N : ℕ} {x y : GaussianInt}
    (h : crsRed N x = crsRed N y) : ((N : ℤ) : GaussianInt) ∣ x - y := by
  have hx : ((N : ℤ) : GaussianInt) ∣ x - crsRed N x := crsRed_dvd N x
  have hy : ((N : ℤ) : GaussianInt) ∣ y - crsRed N y := crsRed_dvd N y
  have h' : ((N : ℤ) : GaussianInt) ∣ (x - crsRed N x) - (y - crsRed N y) := dvd_sub hx hy
  rw [h] at h'
  convert h' using 1
  ring

/-- The fibre over `0` is exactly the kernel `boxK`. -/
lemma crsFib_zero_eq_boxK (M : GaussianInt) :
    crsFib M (Work.FIPlan.gnorm M) 0 = boxK M := by
  ext x; simp [crsFib, boxK]

/-- The map `a ↦ crsRed N (a + (t - s))` carries the fibre over `s` into the fibre over `t`. -/
lemma crsFib_mapsTo (M : GaussianInt) (hM : M ≠ 0) (s t : GaussianInt) :
    Set.MapsTo (fun a => crsRed (Work.FIPlan.gnorm M) (a + (t - s)))
      ↑(crsFib M (Work.FIPlan.gnorm M) s) ↑(crsFib M (Work.FIPlan.gnorm M) t) := by
  intro a ha
  simp only [Finset.mem_coe] at ha ⊢
  rw [mem_crsFib] at ha ⊢
  obtain ⟨_, hadvd⟩ := ha
  refine ⟨crsRed_mem_gbox (gnorm_pos hM) _, ?_⟩
  -- `M ∣ (a + (t - s)) - crsRed N (a + (t - s))` and `M ∣ a - s`
  have h1 : ((Work.FIPlan.gnorm M : ℤ) : GaussianInt) ∣
      (a + (t - s)) - crsRed (Work.FIPlan.gnorm M) (a + (t - s)) := crsRed_dvd _ _
  have h3 : M ∣ (a + (t - s)) - crsRed (Work.FIPlan.gnorm M) (a + (t - s)) :=
    dvd_trans (dvd_gnorm M) h1
  have h5 : M ∣ t - crsRed (Work.FIPlan.gnorm M) (a + (t - s)) := by
    have := dvd_sub h3 hadvd
    convert this using 1; ring
  simpa only [neg_sub] using dvd_neg.mpr h5

/-- The same map is injective on the fibre over `s`. -/
lemma crsFib_injOn (M : GaussianInt) (s t : GaussianInt) :
    Set.InjOn (fun a => crsRed (Work.FIPlan.gnorm M) (a + (t - s)))
      ↑(crsFib M (Work.FIPlan.gnorm M) s) := by
  intro a ha b hb heq
  simp only [Finset.mem_coe] at ha hb
  rw [mem_crsFib] at ha hb
  have hdvd : ((Work.FIPlan.gnorm M : ℤ) : GaussianInt) ∣ (a + (t - s)) - (b + (t - s)) :=
    dvd_of_crsRed_eq heq
  have hdvd' : ((Work.FIPlan.gnorm M : ℤ) : GaussianInt) ∣ a - b := by
    convert hdvd using 1; ring
  exact eq_of_mem_gbox_of_dvd ha.1 hb.1 hdvd'

/-- All fibres of the reduction of the box have the same cardinality. -/
lemma crsFib_card_eq (M : GaussianInt) (hM : M ≠ 0) (s t : GaussianInt) :
    (crsFib M (Work.FIPlan.gnorm M) s).card = (crsFib M (Work.FIPlan.gnorm M) t).card := by
  have hle : (crsFib M (Work.FIPlan.gnorm M) s).card ≤ (crsFib M (Work.FIPlan.gnorm M) t).card :=
    Finset.card_le_card_of_injOn _ (crsFib_mapsTo M hM s t) (crsFib_injOn M s t)
  have hle' : (crsFib M (Work.FIPlan.gnorm M) t).card ≤ (crsFib M (Work.FIPlan.gnorm M) s).card :=
    Finset.card_le_card_of_injOn _ (crsFib_mapsTo M hM t s) (crsFib_injOn M t s)
  exact le_antisymm hle hle'

theorem BoxSumKappa (M : GaussianInt) (hM : M ≠ 0) (S : Finset GaussianInt)
    (hS : Work.FIArea6Hecke.R.IsCRS M S) (f : GaussianInt → ℂ)
    (hf : ∀ z w : GaussianInt, M ∣ (z - w) → f z = f w) :
    Work.FIArea6Hecke.R.boxSum (Work.FIPlan.gnorm M) f =
      ((Work.FIArea6Hecke.R2.kappa M : ℕ) : ℂ) * Finset.sum S f := by
  -- The fibres over distinct elements of `S` are disjoint.
  have hdisj : (S : Set GaussianInt).PairwiseDisjoint
      (fun s => crsFib M (Work.FIPlan.gnorm M) s) := by
    intro a ha b hb hab
    change Disjoint (crsFib M (Work.FIPlan.gnorm M) a) (crsFib M (Work.FIPlan.gnorm M) b)
    rw [Finset.disjoint_left]
    intro x hxa hxb
    rw [mem_crsFib] at hxa hxb
    obtain ⟨s0, ⟨_, _⟩, huniq⟩ := hS a
    have haeq : a = s0 := huniq a ⟨ha, by simp⟩
    have hdvd : M ∣ a - b := by
      have := dvd_sub hxb.2 hxa.2
      convert this using 1; ring
    have hbeq : b = s0 := huniq b ⟨hb, hdvd⟩
    exact hab (by rw [haeq, hbeq])
  -- The fibres cover the box.
  have hunion : S.biUnion (fun s => crsFib M (Work.FIPlan.gnorm M) s)
      = gbox (Work.FIPlan.gnorm M) := by
    apply Finset.Subset.antisymm
    · intro x hx
      rw [Finset.mem_biUnion] at hx
      obtain ⟨s, _, hxs⟩ := hx
      exact (mem_crsFib.mp hxs).1
    · intro x hx
      obtain ⟨s, ⟨hsS, hsdvd⟩, _⟩ := hS x
      rw [Finset.mem_biUnion]
      exact ⟨s, hsS, mem_crsFib.mpr ⟨hx, hsdvd⟩⟩
  rw [Work.FIArea6Hecke.R.boxSum]
  rw [← hunion]
  rw [Finset.sum_biUnion hdisj]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  -- Each fibre contributes `kappa M` copies of `f s`.
  have hcard : (crsFib M (Work.FIPlan.gnorm M) s).card = kappa M := by
    rw [crsFib_card_eq M hM s 0, crsFib_zero_eq_boxK M]
    rfl
  have hconst : ∑ i ∈ crsFib M (Work.FIPlan.gnorm M) s, f i
      = ∑ i ∈ crsFib M (Work.FIPlan.gnorm M) s, f s := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hf i s (mem_crsFib.mp hi).2
  rw [hconst, Finset.sum_const, hcard, nsmul_eq_mul]

end

end Work.FIArea6Hecke.R2
