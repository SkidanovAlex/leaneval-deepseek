/-
  WilG4c — the graph of the junk extension `chi` of a sharp derivative is `Ω`-definable.

  `Work.WilkG4c.chi g L' m` equals the iterated directional derivative `iterDir L' g` on the
  `C^m`-locus of `g` and `0` outside it.  Two facts make its graph an `Ω`-set:

  * the `C^m`-locus `{z | ContDiffAt ℝ m g z}` is *open* (`ContDiffAt.eventually`), so that it
    coincides with `U := interior {z | ContDiffAt ℝ m g z}` and `x ∉ U → ¬ ContDiffAt ℝ m g x`;
  * `U` itself is `Ω`-definable: `SharpDeriv` applied at order `m` (any directions) exhibits the
    graph of the `m`-th derivative over `interior {z | ContDiffAt ℝ m g z}`, whose projection is
    exactly `U` (`S.proj`).

  Hence `graphOf (chi g L' m)` is the union of the `SharpDeriv`-set at order `|L'|` (the graph of
  `iterDir L' g` over `interior {ContDiffAt ℝ |L'|}`) intersected with the lift of `U`, and of
  the lift of `Uᶜ` intersected with `{z last = 0}`.  The identification `iterDir L' g =
  iteratedFDeriv ℝ |L'| g (…single…)` on the `C^{|L'|}`-locus is `iterDir_eq_iteratedFDeriv`.
-/
import Mathlib
import Submission.Work.WilG4c.hbdd_defs
import Submission.Work.WilG4c.iterDir_eq_iteratedFDeriv
import Submission.Work.WilG1.Basic

namespace Work.WilG4c

open WilkiesDesign

/-- The `C^m`-locus of a function is an open condition: a point where `g` is `C^m` lies in the
interior of the `C^m`-locus. -/
theorem mem_interior_contDiffAt {N m : ℕ} {g : (Fin N → ℝ) → ℝ} {x : Fin N → ℝ}
    (h : ContDiffAt ℝ m g x) : x ∈ interior {y : Fin N → ℝ | ContDiffAt ℝ m g y} := by
  rw [mem_interior_iff_mem_nhds]
  exact h.eventually (by simp)

theorem graphOf_chi_mem (S : WilkiesDesign.SOMin) (hder : WilkiesDesign.SOMin.SharpDeriv S)
    {n F D : ℕ} (g : (Fin (n + 1) → ℝ) → ℝ) (hΩ : WilkiesDesign.graphOf g ∈ S.Ω F D (n + 1 + 1))
    (L' : List (Fin (n + 1))) {m : ℕ} (hm : L'.length ≤ m) :
    ∃ (F' D' : ℕ), WilkiesDesign.graphOf (Work.WilkG4c.chi g L' m) ∈ S.Ω F' D' (n + 1 + 1) := by
  obtain ⟨a, b, hsharp⟩ := hder F (n + 1)
  -- the `C^m`-locus of `g` and the `SharpDeriv` witness that it is `Ω`-definable
  set U : Set (Fin (n + 1) → ℝ) := interior {x | ContDiffAt ℝ m g x} with hU
  set Am : Set (Fin (n + 1 + 1) → ℝ) :=
    {z | Fin.init z ∈ interior {x : Fin (n + 1) → ℝ | ContDiffAt ℝ m g x} ∧
      z (Fin.last (n + 1)) =
        iteratedFDeriv ℝ m g (Fin.init z) (fun _ : Fin m => Pi.single (0 : Fin (n + 1)) 1)}
    with hAm
  have hAmmem : Am ∈ S.Ω a (MvPolynomial.eval ![D, m] b) (n + 1 + 1) := by
    rw [hAm]; exact hsharp D g hΩ m (fun _ => 0)
  have hproj : WilkiesDesign.projLast Am = U := by
    ext x
    constructor
    · rintro ⟨t, ht⟩
      rw [hAm] at ht
      simp only [Set.mem_ofPred_eq] at ht
      rw [hU]
      simpa using ht.1
    · intro hx
      refine ⟨iteratedFDeriv ℝ m g x (fun _ : Fin m => Pi.single (0 : Fin (n + 1)) 1), ?_⟩
      rw [hAm]
      simp only [Set.mem_ofPred_eq]
      rw [hU] at hx
      exact ⟨by simpa using hx, by simp⟩
  have hUmem : U ∈ S.Ω (a + 1) (MvPolynomial.eval ![D, m] b) (n + 1) := by
    have h := S.proj hAmmem
    rwa [hproj] at h
  -- the lifted pieces
  set SU : Set (Fin (n + 1 + 1) → ℝ) := {z | Fin.init z ∈ U} with hSU
  have hSUmem : SU ∈ S.Ω (a + 2) (MvPolynomial.eval ![D, m] b) (n + 1 + 1) := by
    rw [hSU]; exact S.prod_right hUmem
  set SUc : Set (Fin (n + 1 + 1) → ℝ) := {z | Fin.init z ∈ Uᶜ} with hSUc
  have hSUcmem : SUc ∈ S.Ω (a + 3) (MvPolynomial.eval ![D, m] b) (n + 1 + 1) := by
    rw [hSUc]; exact S.prod_right (S.compl hUmem)
  set Z0 : Set (Fin (n + 1 + 1) → ℝ) := {z | z (Fin.last (n + 1)) = 0} with hZ0
  have hZ0mem : Z0 ∈ S.Ω (n + 1 + 1) 1 (n + 1 + 1) := by
    have h := S.hyp (n + 1 + 1) (MvPolynomial.X (Fin.last (n + 1)) : MvPolynomial (Fin (n + 1 + 1)) ℝ)
    have hset : {x : Fin (n + 1 + 1) → ℝ | MvPolynomial.eval x
        (MvPolynomial.X (Fin.last (n + 1)) : MvPolynomial (Fin (n + 1 + 1)) ℝ) = 0} = Z0 := by
      rw [hZ0]; ext z; simp
    rw [hset] at h
    simpa using h
  -- the `SharpDeriv`-set at order `|L'|`: the graph of `iterDir L' g` over `int(C^{|L'|})`
  set SD : Set (Fin (n + 1 + 1) → ℝ) :=
    {z | Fin.init z ∈ interior {x : Fin (n + 1) → ℝ | ContDiffAt ℝ L'.length g x} ∧
      z (Fin.last (n + 1)) =
        iteratedFDeriv ℝ L'.length g (Fin.init z) (fun j : Fin L'.length => Pi.single (L'.get j) 1)}
    with hSD
  have hSDmem : SD ∈ S.Ω a (MvPolynomial.eval ![D, L'.length] b) (n + 1 + 1) := by
    rw [hSD]; exact hsharp D g hΩ L'.length L'.get
  -- the set-theoretic description of `graphOf (chi g L' m)`
  have hG_eq : WilkiesDesign.graphOf (Work.WilkG4c.chi g L' m) = (SD ∩ SU) ∪ (SUc ∩ Z0) := by
    ext z
    rw [WilkiesDesign.graphOf]
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff]
    constructor
    · intro hz
      by_cases hzU : Fin.init z ∈ U
      · left
        have hCm : ContDiffAt ℝ m g (Fin.init z) := by rw [hU] at hzU; exact interior_subset hzU
        have hCl : ContDiffAt ℝ L'.length g (Fin.init z) := hCm.of_le (by exact_mod_cast hm)
        have hchi : Work.WilkG4c.chi g L' m (Fin.init z) =
            iteratedFDeriv ℝ L'.length g (Fin.init z)
              (fun j : Fin L'.length => Pi.single (L'.get j) 1) := by
          rw [Work.WilkG4c.chi_of_contDiffAt g L' m hCm,
            iterDir_eq_iteratedFDeriv L' g (Fin.init z) hCl]
        have hSDz : z ∈ SD := by
          rw [hSD]
          exact ⟨mem_interior_contDiffAt hCl, by rw [← hchi]; exact hz⟩
        have hSUz : z ∈ SU := by rw [hSU]; exact hzU
        exact ⟨hSDz, hSUz⟩
      · right
        have hNot : ¬ ContDiffAt ℝ m g (Fin.init z) :=
          fun hc => hzU (by rw [hU]; exact mem_interior_contDiffAt hc)
        have hchi0 : Work.WilkG4c.chi g L' m (Fin.init z) = 0 :=
          Work.WilkG4c.chi_of_not_contDiffAt g L' m hNot
        have hSUcz : z ∈ SUc := by rw [hSUc]; exact hzU
        have hZ0z : z ∈ Z0 := by rw [hZ0]; rw [← hchi0]; exact hz
        exact ⟨hSUcz, hZ0z⟩
    · rintro (⟨hzSD, hzU⟩ | ⟨hzSUc, hzZ0⟩)
      · rw [hSD] at hzSD
        rw [hSU] at hzU
        have hCm : ContDiffAt ℝ m g (Fin.init z) := by rw [hU] at hzU; exact interior_subset hzU
        have hCl : ContDiffAt ℝ L'.length g (Fin.init z) := hCm.of_le (by exact_mod_cast hm)
        have hchi : Work.WilkG4c.chi g L' m (Fin.init z) =
            iteratedFDeriv ℝ L'.length g (Fin.init z)
              (fun j : Fin L'.length => Pi.single (L'.get j) 1) := by
          rw [Work.WilkG4c.chi_of_contDiffAt g L' m hCm,
            iterDir_eq_iteratedFDeriv L' g (Fin.init z) hCl]
        rw [hchi]; exact hzSD.2
      · rw [hSUc] at hzSUc
        rw [hZ0] at hzZ0
        have hNot : ¬ ContDiffAt ℝ m g (Fin.init z) :=
          fun hc => hzSUc (by rw [hU]; exact mem_interior_contDiffAt hc)
        rw [Work.WilkG4c.chi_of_not_contDiffAt g L' m hNot]; exact hzZ0
  -- assemble the membership, bumping everything to common bounds
  set Fc : ℕ := a + (n + 1 + 1) + 10 with hFc
  set Dc : ℕ := max (MvPolynomial.eval ![D, m] b) (MvPolynomial.eval ![D, L'.length] b) + 1 with hDc
  have hDm : MvPolynomial.eval ![D, m] b ≤ Dc := by
    rw [hDc]; exact Nat.le_succ_of_le (le_max_left _ _)
  have hDl : MvPolynomial.eval ![D, L'.length] b ≤ Dc := by
    rw [hDc]; exact Nat.le_succ_of_le (le_max_right _ _)
  have hFa : a ≤ Fc := by rw [hFc]; omega
  have hF2 : a + 2 ≤ Fc := by rw [hFc]; omega
  have hF3 : a + 3 ≤ Fc := by rw [hFc]; omega
  have hFn : n + 1 + 1 ≤ Fc := by rw [hFc]; omega
  have hD1 : 1 ≤ Dc := by rw [hDc]; omega
  have hSD' : SD ∈ S.Ω Fc Dc (n + 1 + 1) := Work.WilG1.Omega.mono hSDmem hFa hDl
  have hSU' : SU ∈ S.Ω Fc Dc (n + 1 + 1) := Work.WilG1.Omega.mono hSUmem hF2 hDm
  have hSUc' : SUc ∈ S.Ω Fc Dc (n + 1 + 1) := Work.WilG1.Omega.mono hSUcmem hF3 hDm
  have hZ0' : Z0 ∈ S.Ω Fc Dc (n + 1 + 1) := Work.WilG1.Omega.mono hZ0mem hFn hD1
  have hP1 : SD ∩ SU ∈ S.Ω (Fc + 1) (Dc + Dc) (n + 1 + 1) := by
    have h := S.inter (F := Fc) (n := n + 1 + 1) (k := 2) (D := fun _ : Fin 2 => Dc)
      (A := fun i : Fin 2 => if i = 0 then SD else SU) (fun i => by
        fin_cases i
        · simpa using hSD'
        · simpa using hSU')
    rw [Fin.sum_univ_two] at h
    rw [Work.WilG1.Omega.iInter_fin_two] at h
    exact h
  have hP2 : SUc ∩ Z0 ∈ S.Ω (Fc + 1) (Dc + Dc) (n + 1 + 1) := by
    have h := S.inter (F := Fc) (n := n + 1 + 1) (k := 2) (D := fun _ : Fin 2 => Dc)
      (A := fun i : Fin 2 => if i = 0 then SUc else Z0) (fun i => by
        fin_cases i
        · simpa using hSUc'
        · simpa using hZ0')
    rw [Fin.sum_univ_two] at h
    rw [Work.WilG1.Omega.iInter_fin_two] at h
    exact h
  have hfin : (SD ∩ SU) ∪ (SUc ∩ Z0) ∈ S.Ω (Fc + 1) ((Dc + Dc) + (Dc + Dc)) (n + 1 + 1) := by
    have h := S.union (F := Fc + 1) (n := n + 1 + 1) (k := 2) (D := fun _ : Fin 2 => Dc + Dc)
      (A := fun i : Fin 2 => if i = 0 then SD ∩ SU else SUc ∩ Z0) (fun i => by
        fin_cases i
        · simpa using hP1
        · simpa using hP2)
    rw [Fin.sum_univ_two] at h
    rw [Work.WilG1.Omega.iUnion_fin_two] at h
    exact h
  exact ⟨Fc + 1, (Dc + Dc) + (Dc + Dc), by rw [hG_eq]; exact hfin⟩

end Work.WilG4c
