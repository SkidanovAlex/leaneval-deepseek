import Mathlib
import Submission.Work.Pi6.Interfaces
import Submission.Work.Pi6.SQASM.Defs
import Submission.Work.Pi6.SQASM.bocksteinFacts
import Submission.Work.Pi6.SQASM.dualityNonzero
import Submission.Work.Pi6.SQASM.fibreModel
import Submission.Work.Pi6.SQASM.connHomology
import Submission.Work.Serre.Assembly.serreK2IntSharp
import Submission.Work.RatHurewicz.isSerreFibration_homotopyFibreFst
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-! Guidance from the project lead (the requester):

AREA SQASM (pi6). Read REFS/NOTES_LEAD_PI6.md §8. Assume SerreRangeLES, EFacts, EMExp, SqCyclicCore, TowerPi.
Statement: with P4, P5 K(ℤ/2,·) models through 12, the Postnikov map g5 : Y → P5 is nonzero on H_7(−;𝔽₂).
Route: K := fibre of homotopyFibreFst g4 (e0 g3) : Y → E over e0 = based loops in P4 (homeomorphic to Path, so a
K(ℤ/2,3) through 11 by Work.Stems.isEMSpaceUpTo_loop; or directly from the fibration LES). SerreRangeLES with R = ZMod 2,
b = 4 (E 3-connected), f = 3: H_6(E;𝔽₂) → H_5(K;𝔽₂) → H_5(Y;𝔽₂) exact, and H_6(E;𝔽₂) = 0 (EFacts: H_6 = ℤ/3, H_5 = 0;
Bockstein sequence) ⇒ the fibre inclusion i is injective on H_5(−;𝔽₂). H_5(K;𝔽₂) ≠ 0 (EMExp: an element of H_5(K;ℤ)
not divisible by 2). g5 is an iso on H_{≤5}(−;ℤ) (Work.Serre.Assembly.serreK2IntSharp: g5 bijective on π_i for i ≤ 5 at
every point) hence on H_{≤5}(−;𝔽₂) (Bockstein five-lemma). So h := g5 ∘ i : K → P5 is nonzero on H_5(−;𝔽₂), hence on
H^5 (duality: kronH_bijective_field + kronH_natural); SqCyclicCore (N = 11, h based) ⇒ h^* ≠ 0 on H^7 ⇒ g5^* ≠ 0 on H^7
⇒ g5_* ≠ 0 on H_7(−;𝔽₂) (duality).
Suggested children: Pi6/SQASM/fibreModel, Pi6/SQASM/injFive, Pi6/SQASM/dualityNonzero.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits

namespace Work.Pi6

open Work.Pi6.SQASM

noncomputable section

theorem sqCyclic (hR : Work.Pi6.SerreRangeLES) (hE : Work.Pi6.EFacts) (hX : Work.Pi6.EMExp)
    (hC : Work.Pi6.SqCyclicCore) (hT : Work.Pi6.TowerPi) : Work.Pi6.SqCyclic := by
  intro P3 _instP3 g3 h3 P4 _instP4 g4 h4 P5 _instP5 g5 h5 hP4em hP5em
  -- connectivity of `E`, `Y` from the killing tower
  obtain ⟨-, hEconn, hYconn, -, -, -⟩ := hT P3 g3 h3 P4 g4 h4 P5 g5 h5
  -- the integral homology of `E` through degree 7
  obtain ⟨-, hE5sub, ⟨eE6⟩, -, -⟩ := hE P3 g3 h3
  -- **the fibre `K` of `Y → E` over `e₀` is a model of `K(ℤ/2,3)` through 11**
  have hKmodel : Work.Serre.IsEMSpaceUpTo (ZMod 2) 3 (by norm_num) 11
      (Kfib g3 g4) (kfibPt g3 g4) := fibreModel g3 g4 hP4em
  have hKconn : ∀ i : ℕ, i ≤ 2 →
      Subsingleton (HomotopyGroup (Fin i) (Kfib g3 g4) (kfibPt g3 g4)) :=
    fun i hi => hKmodel.2 i (by omega) (Or.inl (by omega))
  -- **`K` is 2-connected, so `H₁(K;ℤ) = H₂(K;ℤ) = 0`**
  have hKhom : ∀ i : ℕ, 0 < i → i ≤ 2 →
      CategoryTheory.Limits.IsZero (HR ℤ (Kfib g3 g4) i) :=
    fun i hi hi2 => connHomology (kfibPt g3 g4) 2 i (fun j hj => hKconn j hj) hi hi2
  -- **`H₆(E;𝔽₂) = 0`**: `H₆(E;ℤ) ≅ ℤ/3` is 3-torsion (so `·2` is onto it) and `H₅(E;ℤ) = 0`
  have h3tors : ∀ y : HR ℤ (Ecov g3) 6, (3 : ℤ) • y = 0 := by
    intro y
    refine eE6.injective ?_
    rw [map_zsmul, map_zero]
    have h3 : ((3 : ℤ) : ZMod 3) = 0 := by decide
    rw [zsmul_eq_mul, h3, zero_mul]
  have hsurj2 : Function.Surjective (fun y : ↥(HR ℤ (Ecov g3) 6) => (2 : ℤ) • y) := by
    intro y
    refine ⟨(2 : ℤ) • y, ?_⟩
    show (2 : ℤ) • ((2 : ℤ) • y) = y
    rw [smul_smul]
    have h4 : (2 * 2 : ℤ) • y = y := by
      have h1 : (2 * 2 : ℤ) = 3 + 1 := by norm_num
      rw [h1, add_zsmul, h3tors y, one_smul, zero_add]
    exact h4
  have hsub6cok : Subsingleton ↥(Work.Pi6.HALG.twoCok (HR ℤ (Ecov g3) 6)) :=
    subsingleton_twoCok_of_surjective _ hsurj2
  have hsub5ker : Subsingleton ↥(Work.Pi6.HALG.twoKer (HR ℤ (Ecov g3) 5)) :=
    @subsingleton_twoKer_of_subsingleton _ hE5sub
  have hE6zero : CategoryTheory.Limits.IsZero (HR (ZMod 2) (Ecov g3) 6) :=
    isZero_modTwo_of_subsingleton (Ecov g3) 5 hsub6cok hsub5ker
  -- **the Serre range sequence of `K → Y → E`** (base `E` 3-connected, fibre `K` 2-connected)
  haveI : Nonempty (Ycov g3 g4) := ⟨y0 g3 g4⟩
  have hisSerre : Work.StemsB.IsSerreFibration
      (Work.RatHurewicz.homotopyFibreFst g4 (e0 g3)) :=
    Work.RatHurewicz.isSerreFibration_homotopyFibreFst g4 (e0 g3)
  obtain ⟨bd, hbd⟩ := hR (ZMod 2) (Ycov g3 g4) (Ecov g3)
      (Work.RatHurewicz.homotopyFibreFst g4 (e0 g3)) (y0 g3 g4) 4 3 hisSerre (by norm_num)
      (fun i hi => hEconn i (by omega))
      (hKconn 0 (by norm_num))
      (fun j hj0 hj3 => hKhom j hj0 (by omega))
  have hbd5 : Function.Exact (bd 5).hom
      (hmap (ZMod 2) (kfibIncl g3 g4) 5).hom := by
    have h := (hbd 5 (by norm_num)).2.2
    exact h
  haveI hsub6 : Subsingleton (HR (ZMod 2) (Ecov g3) 6) :=
    ModuleCat.subsingleton_of_isZero hE6zero
  -- **the fibre inclusion is injective on `H₅(−;𝔽₂)`**
  have hinj : Function.Injective (hmap (ZMod 2) (kfibIncl g3 g4) 5).hom :=
    exact_injective_of_subsingleton (bd 5).hom.toAddMonoidHom
      (hmap (ZMod 2) (kfibIncl g3 g4) 5).hom.toAddMonoidHom hbd5 hsub6
  -- **`H₅(K;𝔽₂) ≠ 0`**, from the exponent fact for `K(ℤ/2,3)`
  obtain ⟨a, ha2, hand⟩ := hX.1 (Kfib g3 g4) (kfibPt g3 g4) 11 (by norm_num) hKmodel
  have hKcok : ¬ Subsingleton ↥(Work.Pi6.HALG.twoCok (HR ℤ (Kfib g3 g4) 5)) := by
    intro hsub
    have htop : LinearMap.range (Work.Pi6.HALG.mulTwo (HR ℤ (Kfib g3 g4) 5)).hom = ⊤ :=
      Submodule.Quotient.subsingleton_iff.mp hsub
    have hmem : a ∈ LinearMap.range (Work.Pi6.HALG.mulTwo (HR ℤ (Kfib g3 g4) 5)).hom := by
      rw [htop]
      trivial
    obtain ⟨b, hb⟩ := hmem
    exact hand b (by rw [← Work.Pi6.HALG.mulTwo_apply b]; exact hb)
  have hK5ne : ∃ c : HR (ZMod 2) (Kfib g3 g4) 5, c ≠ 0 :=
    exists_ne_zero_modTwo_of_not_subsingleton_cok (Kfib g3 g4) 4 hKcok
  -- **`g₅` is an isomorphism on `H_{≤5}(−;ℤ)`** (range Whitehead for the `π`-isomorphism `g₅`)
  have hg5int : ∀ i : ℕ, 0 < i → i < 6 → IsIso (hmap ℤ g5 i) :=
    Work.Serre.Assembly.serreK2IntSharp g5 6 (fun i hi y => h5.1 i (by omega) y)
  -- **hence an isomorphism on `H₅(−;𝔽₂)`** (the Bockstein five statement)
  have hg5two : IsIso (hmap (ZMod 2) g5 5) :=
    isIso_modTwo_of_isIso_int g5 4 (hg5int 4 (by norm_num) (by norm_num))
      (hg5int 5 (by norm_num) (by norm_num))
  have hg5inj5 : Function.Injective (hmap (ZMod 2) g5 5).hom :=
    (ModuleCat.mono_iff_injective _).mp (inferInstance : Mono (hmap (ZMod 2) g5 5))
  -- **the composite `h = g₅ ∘ i : K → P₅` is non-zero on `H₅(−;𝔽₂)`**
  have hcomp5 : hmap (ZMod 2) (hcomp g3 g4 g5) 5 ≠ 0 := by
    obtain ⟨c, hc⟩ := hK5ne
    rw [ne_zero_iff_exists_apply_ne_zero]
    refine ⟨c, ?_⟩
    rw [hmap_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
    intro h
    have h1 : (hmap (ZMod 2) g5 5).hom ((hmap (ZMod 2) (kfibIncl g3 g4) 5).hom c)
        = (hmap (ZMod 2) g5 5).hom ((hmap (ZMod 2) (kfibIncl g3 g4) 5).hom 0) := by
      rw [map_zero, h, map_zero]
    exact hc (hinj (hg5inj5 h1))
  -- **duality**: non-vanishing on `H₅` is non-vanishing on `H⁵`
  have hcomp5' : cmap (ZMod 2) (hcomp g3 g4 g5) 5 ≠ 0 :=
    (dualityNonzero (ZMod 2) (hcomp g3 g4 g5) 5).mpr hcomp5
  -- **the Steenrod-squared input** `Sq²Sq²ι₃ ≠ 0` in the form of `SqCyclicCore`
  have hcomp7' : cmap (ZMod 2) (hcomp g3 g4 g5) 7 ≠ 0 :=
    hC (Kfib g3 g4) P5 (kfibPt g3 g4) (g5 (y0 g3 g4)) 11 (by norm_num)
      hKmodel (isEMSpaceUpTo_mono (by norm_num) (by norm_num) (g5 (y0 g3 g4)) hP5em)
      (hcomp g3 g4 g5) rfl hcomp5'
  -- **`g₅^* ≠ 0` on `H⁷`**, since `h^* = i^* ∘ g₅^*`
  have hg57' : cmap (ZMod 2) g5 7 ≠ 0 := by
    intro h
    exact hcomp7' (by rw [cmap_comp, h]; simp)
  -- **and hence `g₅` is non-zero on `H₇(−;𝔽₂)`**
  exact (dualityNonzero (ZMod 2) g5 7).mp hg57'

end

end Work.Pi6
