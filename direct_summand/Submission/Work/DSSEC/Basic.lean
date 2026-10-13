import Mathlib
import Submission.Work.DSMap.Mix2

/-!
# DSSEC — the point-to-blowup chart comparison (node `SEC` of MIX2)

Subproject `DSSEC` builds the vocabulary and the theory for the frozen node

```
DSMap.Mix2.area_SEC p A X f N i hi hif j W hW ψ θ hθ t ht htθ :
  ∃ χ : cechZ A X f (chartCover i) ⟶ chartCechA ψ t, <coaugmentation compatibility>
```

(see `Submission/Work/DSMap/Mix2.lean`).  Mathematically, the node says: a point of the
chart `U_j = X ∩ D₊(x_j)` with values in `W[1/p]` (`W` `p`-torsion-free) and homogeneous
coordinates `t_k ∈ W` gives ring maps

`Γ(X, U_S) ⟶ W[J/t_S] ⊂ W_{t_S}`, `x_k/x_i ↦ t_k/t_i`  (`U_S = ⋂_{i∈S} U_i`, `J = (t_k)`),
for every **nonempty** index set `S`, compatible with restrictions and with the
coaugmentation `A ⟶ W`; equivalently a chain map of Čech complexes over `A`.

## Design of this directory

The node splits into a geometric half and a combinatorial half, glued by the structure
`Work.DSSEC.SecData` of this file (a chart comparison defined on nonempty index sets only —
at `S = ∅` a map `Γ(X, 𝒪_X) → W` need not exist, so the comparison cannot be a natural
transformation on all of `(Finset ι)ᵒᵖ`):

* **geometric half** (`Work.DSSEC.exists_secData`, proved in the sibling modules):
  the SEC hypotheses produce a `SecData`.  It rests on the generation of `Γ(X, U_S)` by the
  chart coordinates `x_k/x_i` (`i ∈ S`) and on the identity
  `(x_k/x_i)·(x_i/x_j) = (x_k/x_j)` in `Γ(X, U_i ∩ U_j)`, together with the coordinates
  `t_k = t_j · θ(x_k/x_j)` supplied by `htθ`.
* **combinatorial half** (`Work.DSSEC.exists_cechMap_of_secData`): a `SecData` produces the
  desired chain map.  The Čech complexes are Mathlib's `cechComplexFunctor`-complexes, and
  the components of the differential are `Work.DSF1.Cech.cechComplexFunctor_d_π`.

## Vocabulary of this file

* `Work.DSSEC.Idx N` — the index type `ULift.{a} (Fin (N+1))` of the SEC complexes.
* `Work.DSSEC.xiSecS i S l hl k` — the section `x_k / x_l` on `⋂_{m ∈ S} U_m` (`l ∈ S`).
* `Work.DSSEC.chartFrac t S l hl k` — the element `t_k / t_l` of `W_{t_S}` (`l ∈ S`), and
  `Work.DSSEC.chartFrac_mem` — it lies in the chart ring `W[J/t_S]`.
* `Work.DSSEC.chartRes t h` — the restriction `chartRing t S →ₐ[W] chartRing t T` for
  `S ⊆ T`.
* `Work.DSSEC.SecData` — the nonempty-index chart comparison used by both halves.
-/

open CategoryTheory AlgebraicGeometry Limits Opposite

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Work.DSSEC
open DSMap DSMap.Mix2

set_option linter.unusedSectionVars false

universe a v

/-- The index type of the SEC complexes: `Fin (N+1)` lifted to universe `a` (so that it lives
in the same universe as `A`, `X` and `W`, as in the frozen node `DSMap.Mix2.area_SEC`). -/
abbrev Idx (N : ℕ) : Type a := ULift.{a} (Fin (N + 1))

section IndexLemmas

variable {A : Type a} [CommRing A] {X : Scheme.{a}} {N : ℕ}

lemma iInf_chartCover_le (i : X ⟶ PSpace A N) {S T : Finset (Idx N)} (h : S ⊆ T) :
    (⨅ m ∈ T, chartCover i m) ≤ (⨅ m ∈ S, chartCover i m) :=
  le_iInf fun m => le_iInf fun hm => iInf_le_of_le m (iInf_le_of_le (h hm) le_rfl)

lemma iInf_chartCover_le_single (i : X ⟶ PSpace A N) {S : Finset (Idx N)} {l : Idx N}
    (hl : l ∈ S) : (⨅ m ∈ S, chartCover i m) ≤ chartCover i l :=
  iInf_le_of_le l (iInf_le_of_le hl le_rfl)

/-- The section `x_k / x_l` on the open `⋂_{m ∈ S} U_m`, for `l ∈ S`: the pullback of the
chart coordinate `x_k / x_l ∈ Γ(X, U_l)` along the inclusion `⋂_{m∈S} U_m ⊆ U_l`. -/
noncomputable def xiSecS (i : X ⟶ PSpace A N) (S : Finset (Idx N)) (l : Idx N) (hl : l ∈ S)
    (k : Idx N) : Γ(X, ⨅ m ∈ S, chartCover i m) :=
  (X.presheaf.map (homOfLE (iInf_chartCover_le_single i hl)).op).hom (xiSec i l.down k.down)

@[simp]
lemma xiSecS_spec (i : X ⟶ PSpace A N) (S : Finset (Idx N)) (l : Idx N) (hl : l ∈ S)
    (k : Idx N) :
    (X.presheaf.map (homOfLE (iInf_chartCover_le_single i hl)).op).hom (xiSec i l.down k.down) =
      xiSecS i S l hl k := rfl

end IndexLemmas

section Chart

variable {W : Type a} [CommRing W] {ι : Type a} [DecidableEq ι]

lemma tS_dvd_of_mem (t : ι → W) {S : Finset ι} {l : ι} (hl : l ∈ S) : t l ∣ tS t S :=
  Finset.dvd_prod_of_mem (fun i => t i) hl

/-- The element `t_l ∈ W` is a unit of the localization `W_{t_S}` as soon as `l ∈ S`. -/
lemma isUnit_algebraMap_t (t : ι → W) {S : Finset ι} {l : ι} (hl : l ∈ S) :
    IsUnit (algebraMap W (Localization.Away (tS t S)) (t l)) :=
  isUnit_of_dvd_unit (map_dvd (algebraMap W (Localization.Away (tS t S))) (tS_dvd_of_mem t hl))
    (IsLocalization.Away.algebraMap_isUnit (R := W) (S := Localization.Away (tS t S)) (tS t S))

/-- The chosen inverse of `t_l` in `W_{t_S}`, for `l ∈ S`. -/
noncomputable def chartUnit (t : ι → W) (S : Finset ι) (l : ι) (hl : l ∈ S) :
    Units (Localization.Away (tS t S)) :=
  IsUnit.unit (isUnit_algebraMap_t t hl)

@[simp]
lemma chartUnit_spec (t : ι → W) (S : Finset ι) (l : ι) (hl : l ∈ S) :
    ↑(chartUnit t S l hl) = algebraMap W (Localization.Away (tS t S)) (t l) :=
  IsUnit.unit_spec _

/-- The chart coordinate `t_k / t_l ∈ W_{t_S}`, for `l ∈ S`.  It lies in the chart ring
`W[J/t_S]` (`Work.DSSEC.chartFrac_mem`), where it is the element characterised by
`(t_k/t_l)·t_l = t_k` (`Work.DSSEC.chartFrac_mul`). -/
noncomputable def chartFrac (t : ι → W) (S : Finset ι) (l : ι) (hl : l ∈ S) (k : ι) :
    Localization.Away (tS t S) :=
  algebraMap W _ (t k) * ↑((chartUnit t S l hl)⁻¹)

/-- The defining property of `t_k / t_l`: `(t_k/t_l)·t_l = t_k`. -/
theorem chartFrac_mul (t : ι → W) (S : Finset ι) (l : ι) (hl : l ∈ S) (k : ι) :
    chartFrac t S l hl k * algebraMap W _ (t l) = algebraMap W _ (t k) := by
  rw [chartFrac, mul_assoc, ← chartUnit_spec t S l hl, Units.inv_mul, mul_one]

/-- The chart coordinate `t_k/t_l` lies in the chart ring `W[J/t_S] ⊂ W_{t_S}`. -/
theorem chartFrac_mem (t : ι → W) (S : Finset ι) (l : ι) (hl : l ∈ S) (k : ι) :
    chartFrac t S l hl k ∈ chartRing t S := by
  rw [chartRing]
  exact Algebra.subset_adjoin (s := chartGens t S) ⟨l, hl, k, chartFrac_mul t S l hl k⟩

/-- The restriction map of blowup charts: `W[J/t_S] → W[J/t_T]` for `S ⊆ T`. -/
noncomputable def chartRes (t : ι → W) {S T : Finset ι} (h : S ⊆ T) :
    chartRing t S →ₐ[W] chartRing t T :=
  AlgHom.codRestrict ((locRes t h).comp (Subalgebra.val (chartRing t S))) (chartRing t T)
    (fun x => chartRing_map_le t h ⟨x.1, x.2, rfl⟩)

@[simp]
lemma chartRes_apply (t : ι → W) {S T : Finset ι} (h : S ⊆ T) (x : chartRing t S) :
    ↑(chartRes t h x) = locRes t h x := rfl

end Chart

section Cmp

variable {W : Type a} [CommRing W] {ι : Type a} [DecidableEq ι]

/-- The **comparison ring** `W[1/(p·t_S)]` in which `W[1/p]`, `W_{t_S}` and the chart ring
`W[J/t_S]` can all be compared: it is the localization of `W` at the powers of `p·t_S`. -/
noncomputable abbrev cmpRing (p : ℕ) (t : ι → W) (S : Finset ι) : Type a :=
  Localization.Away ((p : W) * tS t S)

/-- `W_{t_S} → W[1/(p·t_S)]`. -/
noncomputable def cmpOfLoc (p : ℕ) (t : ι → W) (S : Finset ι) :
    Localization.Away (tS t S) →+* cmpRing p t S :=
  IsLocalization.Away.lift (tS t S) (g := algebraMap W (cmpRing p t S))
    (IsLocalization.Away.isUnit_of_dvd ((p : W) * tS t S) (r := tS t S) (dvd_mul_left _ _))

/-- `W[1/p] → W[1/(p·t_S)]`. -/
noncomputable def cmpOfW (p : ℕ) (t : ι → W) (S : Finset ι) :
    Localization.Away (p : W) →+* cmpRing p t S :=
  IsLocalization.Away.lift ((p : W)) (g := algebraMap W (cmpRing p t S))
    (IsLocalization.Away.isUnit_of_dvd ((p : W) * tS t S) (r := (p : W)) (dvd_mul_right _ _))

/-- The comparison map of the chart ring `W[J/t_S] → W[1/(p·t_S)]`. -/
noncomputable def chartToCmp (p : ℕ) (t : ι → W) (S : Finset ι) :
    chartRing t S →+* cmpRing p t S :=
  (cmpOfLoc p t S).comp (Subalgebra.val (chartRing t S))

@[simp]
lemma cmpOfW_eq (p : ℕ) (t : ι → W) (S : Finset ι) (w : W) :
    cmpOfW p t S (algebraMap W (Localization.Away (p : W)) w) = algebraMap W (cmpRing p t S) w := by
  rw [cmpOfW]
  exact IsLocalization.Away.lift_eq _ _ w

@[simp]
lemma cmpOfLoc_eq (p : ℕ) (t : ι → W) (S : Finset ι) (w : W) :
    cmpOfLoc p t S (algebraMap W (Localization.Away (tS t S)) w) =
      algebraMap W (cmpRing p t S) w := by
  rw [cmpOfLoc]
  exact IsLocalization.Away.lift_eq _ _ w

/-- The element `t_l` is invertible in the comparison ring, for `l ∈ S`. -/
lemma isUnit_cmp_t (p : ℕ) (t : ι → W) (S : Finset ι) {l : ι} (hl : l ∈ S) :
    IsUnit (algebraMap W (cmpRing p t S) (t l)) :=
  isUnit_of_dvd_unit (map_dvd _ (tS_dvd_of_mem t hl))
    (isUnit_of_dvd_unit (map_dvd _ (dvd_mul_left _ _))
      (IsLocalization.Away.algebraMap_isUnit (R := W) (S := cmpRing p t S) ((p : W) * tS t S)))

/-- `chartToCmp` maps `t_k/t_l` to the quotient of the images of `t_k` and `t_l`. -/
lemma chartToCmp_chartFrac (p : ℕ) (t : ι → W) (S : Finset ι) (l : ι) (hl : l ∈ S) (k : ι) :
    chartToCmp p t S ⟨chartFrac t S l hl k, chartFrac_mem t S l hl k⟩ *
        algebraMap W (cmpRing p t S) (t l) = algebraMap W (cmpRing p t S) (t k) := by
  have h := congrArg (fun x : Localization.Away (tS t S) => cmpOfLoc p t S x)
    (chartFrac_mul t S l hl k)
  simp only [map_mul] at h
  show cmpOfLoc p t S (chartFrac t S l hl k) * algebraMap W (cmpRing p t S) (t l) =
    algebraMap W (cmpRing p t S) (t k)
  rw [← cmpOfLoc_eq p t S (t l), h, cmpOfLoc_eq p t S (t k)]

end Cmp

section SecFun

variable (A : Type a) [CommRing A] (X : Scheme.{a}) (f : X ⟶ Spec (.of A)) (N : ℕ)
  (i : X ⟶ PSpace A N) (W : Type a) [CommRing W] (ψ : A →+* W) (t : Idx N → W)

/-- **A chart comparison together with its values on the chart generators** — the intermediate
data produced by the geometric half of node `SEC` (`Work.DSSEC.exists_secData`): the maps
`g S : Γ(X, U_S) → W[J/t_S]` are pinned down by `x_k/x_i ↦ t_k/t_i` (`val_xiSecS`) and agree
with `ψ` on constants (`comm_A`).  Adding the generation of `Γ(X, U_S)` by the chart generators
(`Work.DSSEC.adjoin_xiSecS_eq_top`) turns any `SecFun` into a `SecData`. -/
structure SecFun where
  /-- the chart comparison on nonempty index sets. -/
  toFun : ∀ (S : Finset (Idx N)), S.Nonempty → (Γ(X, ⨅ m ∈ S, chartCover i m) →+* chartRing t S)
  /-- the comparison agrees with `ψ` on the image of `A`. -/
  comm_A : ∀ (S : Finset (Idx N)) (hS : S.Nonempty),
    (toFun S hS).comp (phiU A X f (⨅ m ∈ S, chartCover i m)) =
      (algebraMap W (chartRing t S)).comp ψ
  /-- the value of the comparison on the chart generators `x_k / x_l`, `l ∈ S`. -/
  val_xiSecS : ∀ (S : Finset (Idx N)) (hS : S.Nonempty) (l : Idx N) (hl : l ∈ S) (k : Idx N),
    toFun S hS (xiSecS i S l hl k) =
      ⟨chartFrac t S l hl k, chartFrac_mem t S l hl k⟩

end SecFun

section SecData

variable (A : Type a) [CommRing A] (X : Scheme.{a}) (f : X ⟶ Spec (.of A)) (N : ℕ)
  (i : X ⟶ PSpace A N) (W : Type a) [CommRing W] (ψ : A →+* W) (t : Idx N → W)

/-- **The nonempty-index chart comparison** (the interface between the geometric half and the
combinatorial half of node `SEC`).

`toFun S hS : Γ(X, U_S) →+* W[J/t_S]` is defined for every **nonempty** `S : Finset (Idx N)`
only: at `S = ∅` the analogous map `Γ(X, 𝒪_X) → W` need not exist, and the Čech complexes
never use it.  The two requirements are

* `comm_A` — the comparison agrees with `ψ` on the constants `A ⊂ Γ(X, U_S)`;
* `natural` — the comparisons are compatible with the restriction maps. -/
structure SecData where
  /-- the chart comparison on nonempty index sets. -/
  toFun : ∀ (S : Finset (Idx N)), S.Nonempty → (Γ(X, ⨅ m ∈ S, chartCover i m) →+* chartRing t S)
  /-- the comparison agrees with `ψ` on the image of `A`. -/
  comm_A : ∀ (S : Finset (Idx N)) (hS : S.Nonempty),
    (toFun S hS).comp (phiU A X f (⨅ m ∈ S, chartCover i m)) =
      (algebraMap W (chartRing t S)).comp ψ
  /-- the comparisons are compatible with the restriction maps `S ⊆ T` (`U_T ⊆ U_S`, so the
  restriction goes from the comparison on `S` to the comparison on `T`). -/
  natural : ∀ (S T : Finset (Idx N)) (hS : S.Nonempty) (hST : S ⊆ T)
      (x : Γ(X, ⨅ m ∈ S, chartCover i m)),
    (toFun T (hS.imp fun _ hm => hST hm))
        ((X.presheaf.map (homOfLE (iInf_chartCover_le i hST)).op).hom x) =
      (chartRes t hST) ((toFun S hS) x)

variable {A X f N i W ψ t}

/-- `SecData.toFun S hS` is `A`-linear for the `A`-structures induced by `phiU` and by `ψ`
(this is what the chain map of `Work.DSSEC.exists_cechMap_of_secData` uses). -/
lemma SecData.toFun_smul (D : SecData A X f N i W ψ t) (S : Finset (Idx N)) (hS : S.Nonempty)
    (a : A) (x : Γ(X, ⨅ m ∈ S, chartCover i m)) :
    D.toFun S hS (phiU A X f (⨅ m ∈ S, chartCover i m) a *
        x) = algebraMap W (chartRing t S) (ψ a) * D.toFun S hS x := by
  have h := RingHom.congr_fun (D.comm_A S hS) a
  simp only [RingHom.comp_apply] at h
  rw [map_mul, h]

end SecData

end Work.DSSEC
