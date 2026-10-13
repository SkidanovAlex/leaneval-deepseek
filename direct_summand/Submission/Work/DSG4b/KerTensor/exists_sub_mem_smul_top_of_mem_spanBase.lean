import Mathlib
import Submission.Work.DSM2b.FlatSetup
import Submission.Work.DSM2b.syzygy_helper

namespace Work.DSG4b.KerTensor

universe u

/-- **Base change + Artin–Rees, general ideal.** Let `R` be a commutative ring, `I ⊆ R` an ideal,
`B` an `R`-algebra, `g : R^k → R^m` a map of coordinate modules, and suppose the elementwise
Artin–Rees property holds for `g`, `I` and the shift `c`: for every `N` and every `x : R^k` whose
image `g x` has all coordinates in `I ^ N`, there is `z ∈ I ^ (N - c) • ⊤` with
`x - z ∈ ker g`.

Then every `z : (B ⧸ I^n B)^k` lying in the `(B ⧸ I^n B)`-span of `ker (coordBase g)` (base
changed to `S = R ⧸ I ^ n`) differs from the reduction of some `w ∈ spanBase (ker g) ⊆ B^k` by an
element of `I ^ (n - c) • (B ⧸ I^n B)^k`.

The declaration should live in `namespace Work.DSG4b.KerTensor` (file
`Submission/Work/DSG4b/KerTensor/exists_sub_mem_smul_top_of_mem_spanBase.lean`). -/
lemma exists_sub_mem_smul_top_of_mem_spanBase {R B : Type u} [CommRing R] [CommRing B]
    [Algebra R B] (I : Ideal R) {k m : ℕ} (g : (Fin k → R) →ₗ[R] (Fin m → R)) (c n : ℕ)
    (hAR : ∀ N (x : Fin k → R), (∀ i, g x i ∈ I ^ N) →
      ∃ z ∈ I ^ (N - c) • (⊤ : Submodule R (Fin k → R)), x - z ∈ LinearMap.ker g)
    {z : Fin k → B ⧸ (I ^ n).map (algebraMap R B)}
    (hz : z ∈ Work.DSM2b.spanBase (R := R ⧸ I ^ n) (B := B ⧸ (I ^ n).map (algebraMap R B))
      (LinearMap.ker (Work.DSM2b.coordBase (R := R) (B := R ⧸ I ^ n) g))) :
    ∃ w : Fin k → B, w ∈ Work.DSM2b.spanBase (R := R) (B := B) (LinearMap.ker g) ∧
      z - (fun i => Ideal.Quotient.mk ((I ^ n).map (algebraMap R B)) (w i)) ∈
        (Ideal.map (algebraMap R (B ⧸ (I ^ n).map (algebraMap R B))) (I ^ (n - c))) •
          (⊤ : Submodule (B ⧸ (I ^ n).map (algebraMap R B))
            (Fin k → B ⧸ (I ^ n).map (algebraMap R B))) := by
  classical
  let J : Ideal B := (I ^ n).map (algebraMap R B)
  let M : Type u := B ⧸ J
  -- It suffices to prove the statement for the generators of the `M`-span of `ker gS`.
  have key : ∀ z0 ∈ Work.DSM2b.spanBase (R := R ⧸ I ^ n) (B := M)
        (LinearMap.ker (Work.DSM2b.coordBase (R := R) (B := R ⧸ I ^ n) g)),
      ∃ w ∈ Work.DSM2b.spanBase (R := R) (B := B) (LinearMap.ker g),
        Work.DSM2b.coeffMap (R := B) (B := M) w - z0 ∈
          (Ideal.map (algebraMap R M) (I ^ (n - c))) • (⊤ : Submodule M (Fin k → M)) := by
    intro z0 hz0
    rw [Work.DSM2b.spanBase] at hz0
    refine Submodule.span_induction (p := fun x _ => ∃ w ∈ Work.DSM2b.spanBase (R := R) (B := B)
        (LinearMap.ker g), Work.DSM2b.coeffMap (R := B) (B := M) w - x ∈
          (Ideal.map (algebraMap R M) (I ^ (n - c))) • (⊤ : Submodule M (Fin k → M)))
      ?_ ?_ ?_ ?_ hz0
    · -- generators: elements of the image of `ker gS`
      rintro v ⟨s, hs, rfl⟩
      obtain ⟨x, hx⟩ := Work.DSM2b.exists_coeffMap_eq R (I ^ n) s
      have hs0 : Work.DSM2b.coordBase (R := R) (B := R ⧸ I ^ n) g s = 0 :=
        LinearMap.mem_ker.mp hs
      -- the lift `x` satisfies `g x ∈ (I ^ n)^m` coordinatewise
      have hgx : ∀ i, g x i ∈ I ^ n := by
        intro i
        have h0 : (Work.DSM2b.coordBase (R := R) (B := R ⧸ I ^ n) g
            (Work.DSM2b.coeffMap (R := R) (B := R ⧸ I ^ n) x)) i = 0 := by
          rw [hx]
          exact congrFun hs0 i
        rw [Work.DSM2b.coordBase_apply] at h0
        have hmat : algebraMap R (R ⧸ I ^ n) ((g x) i) =
            ∑ j, algebraMap R (R ⧸ I ^ n) ((g (Pi.single j 1)) i) *
              (Work.DSM2b.coeffMap (R := R) (B := R ⧸ I ^ n) x) j := by
          rw [Work.DSM2b.apply_eq_sum_single_fin g x i, map_sum]
          exact Finset.sum_congr rfl fun j _ => by
            rw [map_mul, Work.DSM2b.coeffMap_apply]
        have h1 : algebraMap R (R ⧸ I ^ n) ((g x) i) = 0 := by
          rw [hmat]; exact h0
        rw [Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem] at h1
        exact h1
      -- Artin–Rees corrects `x` to an element of `ker g` up to `I ^ (n - c)`
      obtain ⟨z', hz'mem, hz'ker⟩ := hAR n x hgx
      refine ⟨Work.DSM2b.coeffMap (R := R) (B := B) (x - z'),
        Submodule.subset_span ⟨x - z', hz'ker, rfl⟩, ?_⟩
      rw [Work.DSM2b.coeffMap_tower (R := R) (S := B) (M := M) (x - z')]
      have h2 : Work.DSM2b.coeffMap (R := R ⧸ I ^ n) (B := M) s =
          Work.DSM2b.coeffMap (R := R) (B := M) x := by
        rw [← hx]
        exact Work.DSM2b.coeffMap_tower (R := R) (S := R ⧸ I ^ n) (M := M) x
      rw [h2, Work.DSM2b.mem_smul_top_fin_iff]
      intro i
      have h3 : (Work.DSM2b.coeffMap (R := R) (B := M) (x - z') -
          Work.DSM2b.coeffMap (R := R) (B := M) x) i = -algebraMap R M (z' i) := by
        rw [Pi.sub_apply, Work.DSM2b.coeffMap_apply, Work.DSM2b.coeffMap_apply, Pi.sub_apply,
          map_sub]
        ring
      rw [h3]
      exact Submodule.neg_mem _ (Ideal.mem_map_of_mem _
        ((Work.DSM2b.mem_smul_top_fin_iff (I ^ (n - c)) z').mp hz'mem i))
    · refine ⟨0, Submodule.zero_mem _, ?_⟩
      rw [map_zero, sub_zero]
      exact Submodule.zero_mem _
    · rintro a b _ _ ⟨wa, hwa, hba⟩ ⟨wb, hwb, hbb⟩
      refine ⟨wa + wb, Submodule.add_mem _ hwa hwb, ?_⟩
      rw [map_add,
        show Work.DSM2b.coeffMap (R := B) (B := M) wa +
              Work.DSM2b.coeffMap (R := B) (B := M) wb - (a + b) =
            (Work.DSM2b.coeffMap (R := B) (B := M) wa - a) +
              (Work.DSM2b.coeffMap (R := B) (B := M) wb - b) from by abel]
      exact Submodule.add_mem _ hba hbb
    · rintro d a _ ⟨w, hw, hbw⟩
      obtain ⟨d', rfl⟩ := Ideal.Quotient.mk_surjective d
      refine ⟨d' • w, Submodule.smul_mem _ _ hw, ?_⟩
      have h1 : Work.DSM2b.coeffMap (R := B) (B := M) (d' • w) =
          Ideal.Quotient.mk J d' • Work.DSM2b.coeffMap (R := B) (B := M) w := by
        rw [map_smul]
        rfl
      rw [h1, ← smul_sub]
      exact Submodule.smul_mem _ _ hbw
  obtain ⟨w, hw, herr⟩ := key z hz
  refine ⟨w, hw, ?_⟩
  have hcoeff : Work.DSM2b.coeffMap (R := B) (B := M) w =
      (fun i => Ideal.Quotient.mk J (w i)) := by
    funext i
    rw [Work.DSM2b.coeffMap_apply]
    rfl
  rw [← hcoeff, ← neg_sub]
  exact Submodule.neg_mem _ herr

end Work.DSG4b.KerTensor
