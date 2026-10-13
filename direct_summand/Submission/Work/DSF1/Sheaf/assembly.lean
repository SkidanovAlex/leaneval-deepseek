import Mathlib
import Submission.Work.DSF1.Sheaf.CechGen
import Submission.Work.DSF1.Sheaf.clearing
import Submission.Work.DSF1.Sheaf.tildeCompLoc

/-!
# Assembly of the Čech exactness for an arbitrary coefficient presheaf

Given a family `f : ι → R` generating the unit ideal and a presheaf `P` of `R`-modules on
`Spec R` satisfying the componentwise clearing of denominators `CompLoc P (f i)` for every
`i`, the Čech complex `Č(P)` of the family `D (f i)` is exact in positive degrees.

The proof is the coefficient-agnostic version of the assembly of
`Work.DSF1.Cech.cechSpec_quasiIso`: the localized complexes `Č (Qi U P i)` are exact in
positive degrees by the "unit case" (`Work.DSF1.Cech.UnitCase`), and the exactness of `Č(P)`
is deduced from it by clearing denominators (`clearing_surj`, `clearing_ker`) and the
partition of unity.
-/

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped AlgebraicGeometry Simplicial BigOperators

namespace Work.DSF1.Sheaf

universe u

variable {R : Type u} [CommRing R] {ι : Type u} [Fintype ι]

omit [Fintype ι] in
/-- **Partition of unity.**  If for every `i` some power of `f i` times `s` is a boundary in
`Č(P)`, then `s` itself is a boundary, provided the `f i` generate the unit ideal. -/
theorem exists_d_eq_of_localized_gen (f : ι → R) (h : Ideal.span (Set.range f) = ⊤)
    (P : MPSheaf (CommRingCat.of R)) (n : ℕ)
    (s : ↥((cechGen (Work.DSF1.Cech.basicOpens f) P).X (n + 1)))
    (H : ∀ i : ι, ∃ (k : ℕ) (t : ↥((cechGen (Work.DSF1.Cech.basicOpens f) P).X n)),
      ((cechGen (Work.DSF1.Cech.basicOpens f) P).d n (n + 1)).hom t = f i ^ k • s) :
    ∃ t : ↥((cechGen (Work.DSF1.Cech.basicOpens f) P).X n),
      ((cechGen (Work.DSF1.Cech.basicOpens f) P).d n (n + 1)).hom t = s := by
  have hmem : s ∈ LinearMap.range
      ((((cechGen (Work.DSF1.Cech.basicOpens f) P).d n (n + 1))).hom) :=
    Submodule.mem_of_span_eq_top_of_smul_pow_mem _ (Set.range f) h s (fun r => by
      obtain ⟨i, hi⟩ := Set.mem_range.mp r.2
      obtain ⟨k, t, ht⟩ := H i
      refine ⟨k, ?_⟩
      rw [← hi]
      exact ⟨t, ht⟩)
  obtain ⟨t, ht⟩ := hmem
  exact ⟨t, ht⟩

/-- **Descent of exactness along `locGen`.**  If `locGen i s` is a boundary, then some power
of `f i` times `s` is a boundary. -/
theorem exists_pow_smul_mem_range_d_gen (f : ι → R) (P : MPSheaf (CommRingCat.of R))
    (i : ι) (n : ℕ) (s : ↥((cechGen (Work.DSF1.Cech.basicOpens f) P).X (n + 1)))
    (H : ∃ t : ↥((cechGen (Work.DSF1.Cech.basicOpens f)
        (Work.DSF1.Cech.Qi (Work.DSF1.Cech.basicOpens f) P i)).X n),
      ((cechGen (Work.DSF1.Cech.basicOpens f)
        (Work.DSF1.Cech.Qi (Work.DSF1.Cech.basicOpens f) P i)).d n (n + 1)).hom t
        = (locGen (Work.DSF1.Cech.basicOpens f) P i).f (n + 1) s)
    (hC1 : ∀ (m : ℕ) (z : ↥((cechGen (Work.DSF1.Cech.basicOpens f)
        (Work.DSF1.Cech.Qi (Work.DSF1.Cech.basicOpens f) P i)).X m)),
      ∃ (k : ℕ) (t : ↥((cechGen (Work.DSF1.Cech.basicOpens f) P).X m)),
        (locGen (Work.DSF1.Cech.basicOpens f) P i).f m t = f i ^ k • z)
    (hC2 : ∀ (m : ℕ) (t : ↥((cechGen (Work.DSF1.Cech.basicOpens f) P).X m)),
      (locGen (Work.DSF1.Cech.basicOpens f) P i).f m t = 0 → ∃ k : ℕ, f i ^ k • t = 0) :
    ∃ (k : ℕ) (t : ↥((cechGen (Work.DSF1.Cech.basicOpens f) P).X n)),
      ((cechGen (Work.DSF1.Cech.basicOpens f) P).d n (n + 1)).hom t = f i ^ k • s := by
  obtain ⟨t_i, ht_i⟩ := H
  obtain ⟨k, t, ht⟩ := hC1 n t_i
  have hcomm := (locGen (Work.DSF1.Cech.basicOpens f) P i).comm' n (n + 1) (by simp)
  have h1 : (locGen (Work.DSF1.Cech.basicOpens f) P i).f (n + 1)
      (((cechGen (Work.DSF1.Cech.basicOpens f) P).d n (n + 1)).hom t) =
      f i ^ k • ((locGen (Work.DSF1.Cech.basicOpens f) P i).f (n + 1) s) := by
    have hh : ((locGen (Work.DSF1.Cech.basicOpens f) P i).f (n + 1))
        (((cechGen (Work.DSF1.Cech.basicOpens f) P).d n (n + 1)) t) =
        ((cechGen (Work.DSF1.Cech.basicOpens f)
          (Work.DSF1.Cech.Qi (Work.DSF1.Cech.basicOpens f) P i)).d n (n + 1))
          ((locGen (Work.DSF1.Cech.basicOpens f) P i).f n t) := by
      have := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hcomm) t
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using this.symm
    rw [hh, ht, map_smul, ht_i]
  have h2 : (locGen (Work.DSF1.Cech.basicOpens f) P i).f (n + 1)
      ((((cechGen (Work.DSF1.Cech.basicOpens f) P).d n (n + 1)).hom t)
        - f i ^ k • s) = 0 := by
    rw [map_sub, h1, map_smul, sub_self]
  obtain ⟨l, hl⟩ := hC2 (n + 1) _ h2
  refine ⟨k + l, f i ^ l • t, ?_⟩
  have h3 : f i ^ l • ((((cechGen (Work.DSF1.Cech.basicOpens f) P).d n (n + 1)).hom t)
      - f i ^ k • s) = 0 := hl
  have h5 : f i ^ l • ((((cechGen (Work.DSF1.Cech.basicOpens f) P).d n (n + 1)).hom t))
      = f i ^ (l + k) • s := by
    have hh := h3
    rw [smul_sub, smul_smul, ← pow_add] at hh
    exact sub_eq_zero.mp hh
  rw [map_smul, h5, Nat.add_comm l k]

/-- **Exactness in positive degrees from the localized complexes.** -/
theorem exact_of_localized_gen (f : ι → R) (h : Ideal.span (Set.range f) = ⊤)
    (P : MPSheaf (CommRingCat.of R))
    (H : ∀ i : ι, ∀ n : ℕ, ∀ s : ↥((cechGen (Work.DSF1.Cech.basicOpens f)
        (Work.DSF1.Cech.Qi (Work.DSF1.Cech.basicOpens f) P i)).X (n + 1)),
      ((cechGen (Work.DSF1.Cech.basicOpens f)
        (Work.DSF1.Cech.Qi (Work.DSF1.Cech.basicOpens f) P i)).d (n + 1) (n + 2)).hom s = 0 →
        ∃ t : ↥((cechGen (Work.DSF1.Cech.basicOpens f)
          (Work.DSF1.Cech.Qi (Work.DSF1.Cech.basicOpens f) P i)).X n),
          ((cechGen (Work.DSF1.Cech.basicOpens f)
            (Work.DSF1.Cech.Qi (Work.DSF1.Cech.basicOpens f) P i)).d n (n + 1)).hom t = s)
    (hC1 : ∀ i : ι, ∀ (m : ℕ) (z : ↥((cechGen (Work.DSF1.Cech.basicOpens f)
        (Work.DSF1.Cech.Qi (Work.DSF1.Cech.basicOpens f) P i)).X m)),
      ∃ (k : ℕ) (t : ↥((cechGen (Work.DSF1.Cech.basicOpens f) P).X m)),
        (locGen (Work.DSF1.Cech.basicOpens f) P i).f m t = f i ^ k • z)
    (hC2 : ∀ i : ι, ∀ (m : ℕ) (t : ↥((cechGen (Work.DSF1.Cech.basicOpens f) P).X m)),
      (locGen (Work.DSF1.Cech.basicOpens f) P i).f m t = 0 → ∃ k : ℕ, f i ^ k • t = 0) :
    ∀ n : ℕ, ∀ s : ↥((cechGen (Work.DSF1.Cech.basicOpens f) P).X (n + 1)),
      ((cechGen (Work.DSF1.Cech.basicOpens f) P).d (n + 1) (n + 2)).hom s = 0 →
        ∃ t : ↥((cechGen (Work.DSF1.Cech.basicOpens f) P).X n),
          ((cechGen (Work.DSF1.Cech.basicOpens f) P).d n (n + 1)).hom t = s := by
  intro n s hs
  refine exists_d_eq_of_localized_gen f h P n s (fun i => ?_)
  have hcomm := (locGen (Work.DSF1.Cech.basicOpens f) P i).comm' (n + 1) (n + 2) (by simp)
  have hcyc : ((cechGen (Work.DSF1.Cech.basicOpens f)
      (Work.DSF1.Cech.Qi (Work.DSF1.Cech.basicOpens f) P i)).d (n + 1) (n + 2)).hom
      ((locGen (Work.DSF1.Cech.basicOpens f) P i).f (n + 1) s) = 0 := by
    have hh : (locGen (Work.DSF1.Cech.basicOpens f) P i).f (n + 2)
        (((cechGen (Work.DSF1.Cech.basicOpens f) P).d (n + 1) (n + 2)) s) =
        ((cechGen (Work.DSF1.Cech.basicOpens f)
          (Work.DSF1.Cech.Qi (Work.DSF1.Cech.basicOpens f) P i)).d (n + 1) (n + 2))
          ((locGen (Work.DSF1.Cech.basicOpens f) P i).f (n + 1) s) := by
      have := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hcomm) s
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using this.symm
    rw [← hh, hs, map_zero]
  obtain ⟨tᵢ, htᵢ⟩ := H i n _ hcyc
  exact exists_pow_smul_mem_range_d_gen f P i n s ⟨tᵢ, htᵢ⟩ (hC1 i) (hC2 i)

/-- **Čech exactness for `M^~`.**  For a finite family `f` generating the unit ideal, the Čech
complex of the standard cover `D (f i)` of `Spec R` with coefficients in `M^~` is exact in
positive degrees. -/
theorem cechGen_tildePresheaf_exact (R : CommRingCat.{u}) {ι : Type u} [Finite ι]
    (f : ι → R) (hf : Ideal.span (Set.range f) = ⊤) (M : ModuleCat.{u} R) :
    ∀ p : ℕ, ∀ s : ↥((cechGen (Work.DSF1.Cech.basicOpens f) (tildePresheaf M)).X (p + 1)),
      ((cechGen (Work.DSF1.Cech.basicOpens f) (tildePresheaf M)).d (p + 1) (p + 2)).hom s = 0 →
        ∃ t : ↥((cechGen (Work.DSF1.Cech.basicOpens f) (tildePresheaf M)).X p),
          ((cechGen (Work.DSF1.Cech.basicOpens f) (tildePresheaf M)).d p (p + 1)).hom t = s := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  exact exact_of_localized_gen (R := ↥R) (ι := ι) f hf (tildePresheaf M)
    (fun i n s hs =>
      (Work.DSF1.Cech.UnitCase (Work.DSF1.Cech.basicOpens f)
        (Work.DSF1.Cech.Qi (Work.DSF1.Cech.basicOpens f) (tildePresheaf M) i) i
        (Work.DSF1.Cech.isIsoDeletion_Qi (Work.DSF1.Cech.basicOpens f)
          (tildePresheaf M) i)).2.1 n s hs)
    (fun i => clearing_surj (f := f) (P := tildePresheaf M) (i := i)
      (hP := tilde_compLoc (R := R) (M := M) (h := f i)))
    (fun i => clearing_ker (f := f) (P := tildePresheaf M) (i := i)
      (hP := tilde_compLoc (R := R) (M := M) (h := f i)))

end Work.DSF1.Sheaf
