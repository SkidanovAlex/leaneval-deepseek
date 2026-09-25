import Mathlib
import Submission.Work.WingbergH3.Defs

/-!
# `Work.WingbergH3.Dual` -- the 𝔽₂-dual of a pro-`2` group with `m` generators

The *group-theoretic* core of the constructive route to Shafarevich's relation-rank bound:

> if a pro-`2` group `X` has a dense generating family of size `m`, then its 𝔽₂-dual
> `DualTwo X = Hom_cont(X, ℤ/2)` has at most `2 ^ m` elements;

and, consequently,

> if the relation group `H²(G_∅,𝔽₂)` of a pro-`2` group embeds into `DualTwo X`, then
> `dim_{𝔽₂} H²(G_∅,𝔽₂) ≤ m`.

The counting of `DualTwo X` is
`Work.RelatorRank.Cohomology.card_continuousHom_eq_two_pow_generatorRank`
(`= 2 ^ GeneratorRank X`, i.e. the dual of the Frattini quotient `X ⧸ Φ(X)`, a finite elementary
abelian `2`-group of order `2 ^ d(X)`), together with `GeneratorRank X ≤ m` from the given dense
generating family.

## Main declarations

* `Work.WingbergH3.natCard_dualTwo_le_two_pow`;
* `Work.WingbergH3.contH2DimLe_of_card_le`;
* `Work.WingbergH3.contH2DimLe_of_salleKochDetection`;
* `Work.WingbergH3.contH2DimLe_of_constructiveDatum`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open scoped Classical

noncomputable section

namespace Work.WingbergH3

open Work.ConCohomology Work.ShafarevichKoch Work.ClassFieldTower

/-- **The generator rank is at most the size of any dense generating family.**  Immediate from
`GeneratorRank = sInf {d | HasDenseGeneratingFamily Γ d}`. -/
theorem generatorRank_le_card_of_denseGenerating {Γ : Type*} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] {m : ℕ} {gen : Fin m → Γ}
    (hdense : Work.RelatorRank.DenseGenerating gen) :
    Work.RelatorRank.GeneratorRank Γ ≤ m :=
  Nat.sInf_le ⟨gen, hdense⟩

/-- **The `𝔽₂`-dual of a pro-`2` group with a dense generating family of size `m` has at most
`2 ^ m` elements.**  This is the counting form of `H¹(X,𝔽₂) ≅ (X ⧸ Φ(X))^*`: the dual sees only
the Frattini quotient, which has `2 ^ d(X) ≤ 2 ^ m` elements. -/
theorem natCard_dualTwo_le_two_pow {X : Type*} [Group X] [TopologicalSpace X]
    [IsTopologicalGroup X] [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    (hp : Work.RelatorRank.IsProPGroup 2 X) {m : ℕ} {gen : Fin m → X}
    (hdense : Work.RelatorRank.DenseGenerating gen) :
    Nat.card (DualTwo X) ≤ 2 ^ m := by
  have hfg : ∃ d, Work.RelatorRank.HasDenseGeneratingFamily X d := ⟨m, gen, hdense⟩
  rw [Work.RelatorRank.Cohomology.card_continuousHom_eq_two_pow_generatorRank hp hfg]
  exact Nat.pow_le_pow_right (by norm_num) (generatorRank_le_card_of_denseGenerating hdense)

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]

/-- **`H²_cont(Γ,𝔽₂)` is killed by `2`**: it is a quotient of the `2`-cocycles with values in
`ℤ/2`, where every element is its own negative. -/
theorem two_nsmul_contH2 (x : Work.RelatorRank.contH2 Γ) : (2 : ℕ) • x = 0 := by
  letI := Work.RelatorRank.f2TrivialAction Γ
  letI : Work.ConCohomology.IsDiscreteGModule Γ (ZMod 2) :=
    Work.RelatorRank.f2Discrete Γ
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective
    (Work.ConCohomology.B2' Γ (ZMod 2)) x
  rw [← map_nsmul]
  rw [show (2 : ℕ) • z = 0 from by
        refine Subtype.ext ?_
        ext p
        show (2 : ℕ) • (z.1 p) = 0
        exact CharTwo.two_nsmul _,
    map_zero]

/-- **`d₂(G) ≤ r` in the cohomological form** (`ContH2DimLe`), from the cardinality bound alone:
a finite group of order at most `2 ^ r` that is an `𝔽₂`-vector space has order `2 ^ k` with
`k ≤ r`.  The finiteness hypothesis cannot be dropped (`Nat.card` of an infinite type is `0`). -/
theorem contH2DimLe_of_card_le (hfin : Finite (Work.RelatorRank.contH2 Γ)) {r : ℕ}
    (h : Nat.card (Work.RelatorRank.contH2 Γ) ≤ 2 ^ r) :
    Work.RelatorRank.ContH2DimLe Γ r := by
  haveI := hfin
  letI : Module (ZMod 2) (Work.RelatorRank.contH2 Γ) :=
    AddCommGroup.zmodModule (n := 2) (fun x => two_nsmul_contH2 x)
  haveI : Module.Finite (ZMod 2) (Work.RelatorRank.contH2 Γ) := Module.Finite.of_finite
  have hcardfin : Nat.card (Work.RelatorRank.contH2 Γ) =
      2 ^ Module.finrank (ZMod 2) (Work.RelatorRank.contH2 Γ) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  refine ⟨Module.finrank (ZMod 2) (Work.RelatorRank.contH2 Γ), ?_, hcardfin⟩
  have hle : 2 ^ Module.finrank (ZMod 2) (Work.RelatorRank.contH2 Γ) ≤ 2 ^ r := by
    rw [← hcardfin]
    exact h
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hle

/-- **Salle--Koch detection bounds the relation rank.**  If `H²(G,𝔽₂)` embeds into the 𝔽₂-dual of
a pro-`2` group with a dense generating family of size `m`, then `d₂(G) ≤ m`. -/
theorem contH2DimLe_of_salleKochDetection {m : ℕ} (I : InertiaModule m)
    (h : SalleKochDetects Γ I) : Work.RelatorRank.ContH2DimLe Γ m := by
  obtain ⟨φ, hφ⟩ := h
  have hcardX : Nat.card (DualTwo I.X) = 2 ^ Work.RelatorRank.GeneratorRank I.X :=
    Work.RelatorRank.Cohomology.card_continuousHom_eq_two_pow_generatorRank I.proX
      ⟨m, I.gen, I.dense⟩
  have hfinX : Finite (DualTwo I.X) :=
    Nat.finite_of_card_ne_zero (by rw [hcardX]; exact pow_ne_zero _ (by norm_num))
  haveI : Finite (Work.RelatorRank.contH2 Γ) := Finite.of_injective φ hφ
  refine contH2DimLe_of_card_le inferInstance ?_
  calc Nat.card (Work.RelatorRank.contH2 Γ) ≤ Nat.card (DualTwo I.X) :=
        Nat.card_le_card_of_injective φ hφ
    _ ≤ 2 ^ m := natCard_dualTwo_le_two_pow I.proX I.dense

/-- **THE CONSTRUCTIVE ROUTE, group-theoretic end**: the constructive datum bounds the relation
rank of `G_∅` by `d + d₂(O_F^×)` -- i.e. it proves Shafarevich's relation-rank bound in the
cohomological form, with no input from Wingberg duality. -/
theorem contH2DimLe_of_constructiveDatum {F : Type*} [Field F] [NumberField F]
    (D : ConstructiveDatum F) :
    Work.RelatorRank.ContH2DimLe (galoisGroup D.M) (D.d + unitTwoRank F) :=
  contH2DimLe_of_salleKochDetection D.I D.detects

/-- **Shafarevich's relation-rank bound from the constructive datum.** -/
theorem shafarevichBound_of_constructiveDatum {F : Type*} [Field F] [NumberField F]
    (D : ConstructiveDatum F) :
    Work.WingbergRoute.ShafarevichBound F D.M :=
  (Work.WingbergRoute.shafarevichBound_iff F D.M).mpr
    ⟨D.d, D.hd, contH2DimLe_of_constructiveDatum D⟩

end Work.WingbergH3
