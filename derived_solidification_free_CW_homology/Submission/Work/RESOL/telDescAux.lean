/-
AREA RESOL — self-contained copies of the two inputs to `Work.RESOL.quasiIso_telDesc` that live
in files which are still being edited elsewhere in the workspace:

* `Mono (telD P t)` (`telD = 1 - smap` is a monomorphism of complexes);
* `Epi (Hᵏ (cokernel.π (telD P t)))` (the cokernel projection is an epimorphism on homology).

Both are proved in the same way as in `Submission/Work/RESOL/mono_telD.lean` and
`Submission/Work/RESOL/epi_homologyMap_cokernel_telD.lean`, but the inputs they use are taken from
the completed `Work.RESOL.mono_sigmaToPi_light` (`∐ₙ Xₙ ⟶ ∏ₙ Xₙ` is injective) and
`Work.RESOL.isIso_sigmaHomologyMap` (`Hᵏ` commutes with small coproducts), so that

* the statements here rest on completed material only, and
* they do not depend on `Work.RESOL.mono_sigmaToPi` (which is equivalent to
  `mono_sigmaToPi_light` but whose file is not yet finished).

The material is kept in the separate namespace `Work.RESOL.TelDescAux` so that it does not clash
with the originals.
-/
import Mathlib
import Submission.Work.RESOL.Telescope
import Submission.Work.RESOL.Instances
import Submission.Work.TOOLKIT.Sigma.Toolkit
import Submission.Work.RESOL.mono_sigmaToPi_light
import Submission.Work.RESOL.isIso_sigmaHomologyMap

open CategoryTheory Limits LightProfinite LightCondensed
open _root_.LightCondensed

noncomputable section

attribute [local instance 2000] Sheaf.instHasColimitsOfShape

namespace Work.RESOL.TelDescAux

/-! ## The shift of a sequence of light condensed abelian groups -/

/-- The `k`-fold composite of an endomorphism; `iterEnd 0 f = 𝟙 _` and
`iterEnd (k+1) f = iterEnd k f ≫ f`. -/
def iterEnd {C : Type*} [Category C] {X : C} : ℕ → (X ⟶ X) → (X ⟶ X)
  | 0, _ => 𝟙 X
  | (k+1), f => iterEnd k f ≫ f

@[simp]
lemma iterEnd_zero {C : Type*} [Category C] {X : C} (f : X ⟶ X) :
    iterEnd 0 f = 𝟙 X := rfl

@[simp]
lemma iterEnd_succ {C : Type*} [Category C] {X : C} (k : ℕ) (f : X ⟶ X) :
    iterEnd (k+1) f = iterEnd k f ≫ f := rfl

/-- The shift `s : ∐ n, A n ⟶ ∐ n, A n`, characterized by `ι n ≫ s = t n ≫ ι (n+1)`. -/
def shiftAb (A : ℕ → LightCondAb) [HasCoproduct A] (t : ∀ n : ℕ, A n ⟶ A (n+1)) :
    (∐ A) ⟶ (∐ A) :=
  Sigma.desc (fun n => t n ≫ Sigma.ι A (n+1))

lemma Sigma_ι_shiftAb (A : ℕ → LightCondAb) [HasCoproduct A]
    (t : ∀ n : ℕ, A n ⟶ A (n+1)) (n : ℕ) :
    Sigma.ι A n ≫ shiftAb A t = t n ≫ Sigma.ι A (n+1) :=
  Sigma.ι_comp_desc _ n

/-- The shift kills the `0`-th coordinate (nothing lands in the `0`-th summand). -/
lemma shiftAb_comp_coord_zero (A : ℕ → LightCondAb) [HasCoproduct A]
    (t : ∀ n : ℕ, A n ⟶ A (n+1)) : shiftAb A t ≫ coord A 0 = 0 := by
  apply Sigma.hom_ext
  intro n
  rw [← Category.assoc, Sigma_ι_shiftAb, Category.assoc,
    coord_eq_zero_of_ne A (Nat.succ_ne_zero n), comp_zero, comp_zero]

/-- The shift followed by the `(m+1)`-st coordinate is the `m`-th coordinate followed by `t m`. -/
lemma shiftAb_comp_coord_succ (A : ℕ → LightCondAb) [HasCoproduct A]
    (t : ∀ n : ℕ, A n ⟶ A (n+1)) (m : ℕ) :
    shiftAb A t ≫ coord A (m+1) = coord A m ≫ t m := by
  apply Sigma.hom_ext
  intro n
  rw [← Category.assoc, Sigma_ι_shiftAb]
  by_cases h : n = m
  · subst h
    rw [Category.assoc, Sigma_ι_coord_self, Category.comp_id, ← Category.assoc,
      Sigma_ι_coord_self, Category.id_comp]
  · have h2 : ¬ (n + 1 = m + 1) := fun hh => h (Nat.succ.inj hh)
    rw [Category.assoc, coord_eq_zero_of_ne A h2, comp_zero, ← Category.assoc,
      coord_eq_zero_of_ne A h, zero_comp]

/-- The `j`-th coordinate of the `(j+1)`-st iterate of the shift vanishes. -/
lemma shiftAb_iterEnd_comp_coord_zero (A : ℕ → LightCondAb) [HasCoproduct A]
    (t : ∀ n : ℕ, A n ⟶ A (n+1)) (j : ℕ) :
    iterEnd (j+1) (shiftAb A t) ≫ coord A j = 0 := by
  induction j with
  | zero =>
    rw [iterEnd_succ, iterEnd_zero, Category.id_comp]
    exact shiftAb_comp_coord_zero A t
  | succ j ih =>
    rw [iterEnd_succ, Category.assoc, shiftAb_comp_coord_succ, ← Category.assoc, ih, zero_comp]

/-! ## The coordinates jointly detect zero maps -/

lemma eq_zero_of_coord_eq_zero {A : ℕ → LightCondAb} [HasCoproduct A] [HasProduct A]
    (hdet : Mono (sigmaToPi A)) {Z : LightCondAb} (u : Z ⟶ ∐ A)
    (hu : ∀ m : ℕ, u ≫ coord A m = 0) : u = 0 := by
  have h : u ≫ sigmaToPi A = 0 := by
    apply Pi.hom_ext
    intro m
    rw [Category.assoc, Pi_π_sigmaToPi, hu m, zero_comp]
  exact hdet.right_cancellation u 0 (by rw [h, zero_comp])

/-- `u ≫ (1 - s) = 0` forces `u = 0`: the telescope argument, at the level of light condensed
abelian groups. -/
lemma eq_zero_of_comp_oneSub_shiftAb {A : ℕ → LightCondAb} [HasCoproduct A] [HasProduct A]
    (hdet : Mono (sigmaToPi A)) (t : ∀ n : ℕ, A n ⟶ A (n+1)) {Z : LightCondAb}
    (u : Z ⟶ ∐ A) (hu : u ≫ (𝟙 (∐ A) - shiftAb A t) = 0) : u = 0 := by
  have hsub : u - u ≫ shiftAb A t = 0 := by
    rw [← hu, Preadditive.comp_sub, Category.comp_id]
  have hstep : u ≫ shiftAb A t = u := (sub_eq_zero.mp hsub).symm
  have hpow : ∀ k : ℕ, u ≫ iterEnd k (shiftAb A t) = u := by
    intro k
    induction k with
    | zero => rw [iterEnd_zero, Category.comp_id]
    | succ k ih => rw [iterEnd_succ, ← Category.assoc, ih, hstep]
  apply eq_zero_of_coord_eq_zero hdet
  intro m
  rw [← hpow (m + 1), Category.assoc, shiftAb_iterEnd_comp_coord_zero, comp_zero]

/-- The map `1 - s` is a monomorphism, where `s` is the shift of a sequence of light condensed
abelian groups. -/
lemma mono_oneSub_shiftAb {A : ℕ → LightCondAb} [HasCoproduct A] [HasProduct A]
    (hdet : Mono (sigmaToPi A)) (t : ∀ n : ℕ, A n ⟶ A (n+1)) :
    Mono (𝟙 (∐ A) - shiftAb A t) := by
  refine ⟨fun {Z} g h eq => ?_⟩
  have hzero : (g - h) ≫ (𝟙 (∐ A) - shiftAb A t) = 0 := by
    rw [Preadditive.sub_comp, eq, sub_self]
  have h2 : g - h = 0 := eq_zero_of_comp_oneSub_shiftAb hdet t (g - h) hzero
  rwa [sub_eq_zero] at h2

/-! ## The degreewise reduction in `Cpx` -/

variable (P : ℕ → Cpx) [HasCoproduct P] (t : ∀ n : ℕ, P n ⟶ P (n+1))

/-- In degree `k`, the shift of the coproduct complex is the shift of the degreewise family,
up to the canonical isomorphism `Work.TOOLKIT.sigmaXIso`. -/
lemma sigmaXIso_hom_smap_f (k : ℤ) :
    (Work.TOOLKIT.sigmaXIso P k).hom ≫ (smap P t).f k ≫ (Work.TOOLKIT.sigmaXIso P k).inv
      = shiftAb (fun n : ℕ => (P n).X k) (fun n : ℕ => (t n).f k) := by
  apply Sigma.hom_ext
  intro n
  have hι : Sigma.ι (fun n : ℕ => (P n).X k) n ≫ (Work.TOOLKIT.sigmaXIso P k).hom
      = (Sigma.ι P n).f k := by
    rw [← Work.TOOLKIT.sigmaXIso_ι P k n, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hsm : (Sigma.ι P n).f k ≫ (smap P t).f k
      = (t n).f k ≫ (Sigma.ι P (n+1)).f k := by
    rw [← HomologicalComplex.comp_f, Sigma_ι_smap, HomologicalComplex.comp_f]
  calc Sigma.ι (fun j : ℕ => (P j).X k) n
        ≫ ((Work.TOOLKIT.sigmaXIso P k).hom ≫ (smap P t).f k
            ≫ (Work.TOOLKIT.sigmaXIso P k).inv)
      = ((Sigma.ι (fun j : ℕ => (P j).X k) n ≫ (Work.TOOLKIT.sigmaXIso P k).hom)
          ≫ (smap P t).f k) ≫ (Work.TOOLKIT.sigmaXIso P k).inv := by
        simp only [Category.assoc]
    _ = ((Sigma.ι P n).f k ≫ (smap P t).f k) ≫ (Work.TOOLKIT.sigmaXIso P k).inv := by rw [hι]
    _ = ((t n).f k ≫ (Sigma.ι P (n+1)).f k) ≫ (Work.TOOLKIT.sigmaXIso P k).inv := by rw [hsm]
    _ = (t n).f k ≫ ((Sigma.ι P (n+1)).f k ≫ (Work.TOOLKIT.sigmaXIso P k).inv) := by
        simp only [Category.assoc]
    _ = (t n).f k ≫ Sigma.ι (fun j : ℕ => (P j).X k) (n+1) := by
        rw [Work.TOOLKIT.sigmaXIso_ι P k (n+1)]
    _ = Sigma.ι (fun j : ℕ => (P j).X k) n
          ≫ shiftAb (fun j : ℕ => (P j).X k) (fun j : ℕ => (t j).f k) := by
        rw [Sigma_ι_shiftAb]

/-- The degree `k` part of `smap P t`, conjugated by `Work.TOOLKIT.sigmaXIso`. -/
lemma smap_f_eq_conj (k : ℤ) :
    (smap P t).f k
      = (Work.TOOLKIT.sigmaXIso P k).inv
        ≫ shiftAb (fun n : ℕ => (P n).X k) (fun n : ℕ => (t n).f k)
        ≫ (Work.TOOLKIT.sigmaXIso P k).hom := by
  have h := sigmaXIso_hom_smap_f P t k
  rw [← h]
  rw [show (Work.TOOLKIT.sigmaXIso P k).inv
        ≫ ((Work.TOOLKIT.sigmaXIso P k).hom ≫ (smap P t).f k ≫ (Work.TOOLKIT.sigmaXIso P k).inv)
        ≫ (Work.TOOLKIT.sigmaXIso P k).hom
      = ((Work.TOOLKIT.sigmaXIso P k).inv ≫ (Work.TOOLKIT.sigmaXIso P k).hom)
        ≫ (smap P t).f k
        ≫ ((Work.TOOLKIT.sigmaXIso P k).inv ≫ (Work.TOOLKIT.sigmaXIso P k).hom) from by
    simp only [Category.assoc]]
  rw [Iso.inv_hom_id, Category.id_comp, Category.comp_id]

/-- The degree `k` part of `telD P t` is the map `1 - shift` for the degree `k` family. -/
lemma telD_f_eq (k : ℤ) :
    (telD P t).f k
      = (Work.TOOLKIT.sigmaXIso P k).inv
        ≫ (𝟙 (∐ fun n : ℕ => (P n).X k)
            - shiftAb (fun n : ℕ => (P n).X k) (fun n : ℕ => (t n).f k))
        ≫ (Work.TOOLKIT.sigmaXIso P k).hom := by
  have h1 : (telD P t).f k = 𝟙 ((∐ P).X k) - (smap P t).f k := by
    rw [telD]
    simp
  rw [h1, smap_f_eq_conj P t k]
  rw [show (𝟙 ((∐ P).X k)
        - (Work.TOOLKIT.sigmaXIso P k).inv
          ≫ shiftAb (fun n : ℕ => (P n).X k) (fun n : ℕ => (t n).f k)
          ≫ (Work.TOOLKIT.sigmaXIso P k).hom)
      = (Work.TOOLKIT.sigmaXIso P k).inv
        ≫ (𝟙 (∐ fun n : ℕ => (P n).X k)
            - shiftAb (fun n : ℕ => (P n).X k) (fun n : ℕ => (t n).f k))
        ≫ (Work.TOOLKIT.sigmaXIso P k).hom from by
    simp only [Preadditive.comp_sub, Preadditive.sub_comp, Category.id_comp, Category.comp_id,
      Iso.inv_hom_id]]

/-- In each degree, `telD P t` is a monomorphism. -/
lemma mono_telD_f (k : ℤ) (hdet : Mono (sigmaToPi (fun n : ℕ => (P n).X k))) :
    Mono ((telD P t).f k) := by
  rw [telD_f_eq P t k]
  haveI : Mono (𝟙 (∐ fun n : ℕ => (P n).X k)
      - shiftAb (fun n : ℕ => (P n).X k) (fun n : ℕ => (t n).f k)) :=
    mono_oneSub_shiftAb hdet (fun n : ℕ => (t n).f k)
  haveI : Mono ((𝟙 (∐ fun n : ℕ => (P n).X k)
      - shiftAb (fun n : ℕ => (P n).X k) (fun n : ℕ => (t n).f k))
      ≫ (Work.TOOLKIT.sigmaXIso P k).hom) :=
    mono_comp _ _
  exact mono_comp _ _

/-- **`telD P t` is a monomorphism**, from `∐ₙ Xₙ ⟶ ∏ₙ Xₙ` being injective. -/
theorem mono_telD (P : ℕ → Cpx) [HasCoproduct P] (t : ∀ n : ℕ, P n ⟶ P (n+1)) :
    Mono (telD P t) :=
  HomologicalComplex.mono_of_mono_f (telD P t)
    (fun k => mono_telD_f P t k (mono_sigmaToPi_light (fun n : ℕ => (P n).X k)))

/-! ## `Hᵏ` of the cokernel projection of `telD` is an epimorphism -/

/-- For a short exact sequence of cochain complexes `0 → A --f--> A --g--> C → 0` (here `A = A`
and `f` is an endomorphism of `A`), the map on homology `Hᵏ(g)` is an epimorphism as soon as the
map `H^(k+1)(f)` is a monomorphism.  Both are equivalent to the vanishing of the connecting map
`δ : Hᵏ(C) ⟶ H^(k+1)(A)`: this is the exactness of `Hᵏ(A) --g--> Hᵏ(C) --δ--> H^(k+1)(A)` on the
one hand (`ShortComplex.ShortExact.homology_exact₃`), and the exactness of
`Hᵏ(C) --δ--> H^(k+1)(A) --f--> H^(k+1)(A)` on the other
(`ShortComplex.ShortExact.homology_exact₁`). -/
theorem epi_homologyMap_g_of_mono_homologyMap_f {C : Type*} [Category C] [Abelian C]
    {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact) (k : ℤ)
    (h : Mono (HomologicalComplex.homologyMap S.f (k+1))) :
    Epi (HomologicalComplex.homologyMap S.g k) := by
  have hij : (ComplexShape.up ℤ).Rel k (k+1) := by simp
  exact ((hS.homology_exact₃ k (k+1) hij).epi_f_iff).mpr
    (((hS.homology_exact₁ k (k+1) hij).mono_g_iff).mp h)

/-- The `n`-th component of the comparison map `sigmaHomologyMap` is the map induced on homology
by the `n`-th coproduct inclusion. -/
lemma sigmaHomologyMap_comp_ι (P : ℕ → Cpx) [HasCoproduct P] (k : ℤ) (n : ℕ) :
    Sigma.ι (fun m : ℕ => (P m).homology k) n ≫ Work.TOOLKIT.sigmaHomologyMap P k
      = HomologicalComplex.homologyMap (Sigma.ι P n) k := by
  rw [Work.TOOLKIT.sigmaHomologyMap, Limits.Sigma.ι_comp_desc]

/-- **The shift on the coproduct of the homologies.**  Under the comparison map
`sigmaHomologyMap P k`, the map induced on homology by the shift `smap P t` is the shift of the
family of maps `Hᵏ(t n)`. -/
lemma sigmaHomologyMap_smap (P : ℕ → Cpx) [HasCoproduct P] (t : ∀ n : ℕ, P n ⟶ P (n+1))
    (k : ℤ) :
    Work.TOOLKIT.sigmaHomologyMap P k ≫ HomologicalComplex.homologyMap (smap P t) k =
      shiftAb (fun n : ℕ => (P n).homology k)
          (fun n : ℕ => HomologicalComplex.homologyMap (t n) k)
        ≫ Work.TOOLKIT.sigmaHomologyMap P k := by
  have hcomp (n : ℕ) :
      HomologicalComplex.homologyMap (Sigma.ι P n) k
          ≫ HomologicalComplex.homologyMap (smap P t) k
        = HomologicalComplex.homologyMap (t n) k
          ≫ HomologicalComplex.homologyMap (Sigma.ι P (n+1)) k := by
    rw [← HomologicalComplex.homologyMap_comp, Sigma_ι_smap,
      HomologicalComplex.homologyMap_comp]
  have hkey : shiftAb (fun n : ℕ => (P n).homology k)
        (fun n : ℕ => HomologicalComplex.homologyMap (t n) k)
        ≫ Work.TOOLKIT.sigmaHomologyMap P k
      = Limits.Sigma.desc (fun n : ℕ => HomologicalComplex.homologyMap (t n) k
          ≫ HomologicalComplex.homologyMap (Sigma.ι P (n+1)) k) := by
    rw [shiftAb]
    rw [← Work.TOOLKIT.sigma_desc_comp]
    congr 1
    funext n
    rw [Category.assoc, sigmaHomologyMap_comp_ι P k (n+1)]
  rw [hkey]
  show Limits.Sigma.desc (fun n : ℕ => HomologicalComplex.homologyMap (Sigma.ι P n) k)
      ≫ HomologicalComplex.homologyMap (smap P t) k = _
  rw [← Work.TOOLKIT.sigma_desc_comp]
  congr 1
  funext n
  exact hcomp n

/-- **The homology of `1 - shift` is a monomorphism.** -/
lemma mono_homologyMap_telD_of (P : ℕ → Cpx) [HasCoproduct P]
    (t : ∀ n : ℕ, P n ⟶ P (n+1))
    (hdet : ∀ k : ℤ, Mono (sigmaToPi (fun n : ℕ => (P n).homology k)))
    (hiso : ∀ k : ℤ, IsIso (Work.TOOLKIT.sigmaHomologyMap P k)) (k : ℤ) :
    Mono (HomologicalComplex.homologyMap (telD P t) k) := by
  haveI : IsIso (Work.TOOLKIT.sigmaHomologyMap P k) := hiso k
  have hconj := sigmaHomologyMap_smap P t k
  have hfac : Work.TOOLKIT.sigmaHomologyMap P k
        ≫ (𝟙 (HomologicalComplex.homology (∐ P) k)
            - HomologicalComplex.homologyMap (smap P t) k)
      = (𝟙 (∐ fun n : ℕ => (P n).homology k)
            - shiftAb (fun n : ℕ => (P n).homology k)
                (fun n : ℕ => HomologicalComplex.homologyMap (t n) k))
        ≫ Work.TOOLKIT.sigmaHomologyMap P k := by
    rw [Preadditive.comp_sub, Category.comp_id, hconj, Preadditive.sub_comp, Category.id_comp]
  have h2 : HomologicalComplex.homologyMap (telD P t) k
      = 𝟙 (HomologicalComplex.homology (∐ P) k)
        - HomologicalComplex.homologyMap (smap P t) k := by
    rw [telD, HomologicalComplex.homologyMap_sub, HomologicalComplex.homologyMap_id]
  rw [h2]
  haveI hshift : Mono (𝟙 (∐ fun n : ℕ => (P n).homology k)
      - shiftAb (fun n : ℕ => (P n).homology k)
          (fun n : ℕ => HomologicalComplex.homologyMap (t n) k)) :=
    mono_oneSub_shiftAb (hdet k) (fun n : ℕ => HomologicalComplex.homologyMap (t n) k)
  have h3 : Mono (inv (Work.TOOLKIT.sigmaHomologyMap P k)
      ≫ (Work.TOOLKIT.sigmaHomologyMap P k
          ≫ (𝟙 (HomologicalComplex.homology (∐ P) k)
              - HomologicalComplex.homologyMap (smap P t) k))) := by
    haveI : Mono (Work.TOOLKIT.sigmaHomologyMap P k
        ≫ (𝟙 (HomologicalComplex.homology (∐ P) k)
            - HomologicalComplex.homologyMap (smap P t) k)) := by
      rw [hfac]
      infer_instance
    infer_instance
  rw [← Category.assoc, IsIso.inv_hom_id, Category.id_comp] at h3
  exact h3

/-- The map `telD P t = 𝟙 - shift` is a monomorphism as soon as the canonical comparison maps
`∐ₙ (Pₙ)ᵏ ⟶ ∏ₙ (Pₙ)ᵏ` are monomorphisms in every degree. -/
lemma mono_telD_of (P : ℕ → Cpx) [HasCoproduct P] (t : ∀ n : ℕ, P n ⟶ P (n+1))
    (hdet : ∀ k : ℤ, Mono (sigmaToPi (fun n : ℕ => (P n).X k))) :
    Mono (telD P t) :=
  HomologicalComplex.mono_of_mono_f (telD P t) (fun k => mono_telD_f P t k (hdet k))

/-- The cokernel projection of `telD P t` induces an epimorphism on homology in every degree. -/
theorem epi_homologyMap_cokernel_telD_of (P : ℕ → Cpx) [HasCoproduct P]
    (t : ∀ n : ℕ, P n ⟶ P (n+1))
    (hdetX : ∀ k : ℤ, Mono (sigmaToPi (fun n : ℕ => (P n).X k)))
    (hdetH : ∀ k : ℤ, Mono (sigmaToPi (fun n : ℕ => (P n).homology k)))
    (hiso : ∀ k : ℤ, IsIso (Work.TOOLKIT.sigmaHomologyMap P k)) (k : ℤ) :
    Epi (HomologicalComplex.homologyMap (cokernel.π (telD P t)) k) := by
  let S : ShortComplex Cpx :=
    ShortComplex.mk (telD P t) (cokernel.π (telD P t)) (cokernel.condition (telD P t))
  have hmono : Mono S.f := mono_telD_of P t hdetX
  have hepi : Epi S.g := inferInstance
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk'
      (ShortComplex.exact_of_g_is_cokernel S
        (show IsColimit (CokernelCofork.ofπ S.g S.zero) from
          cokernelIsCokernel (telD P t)))
      hmono hepi
  have hh : Mono (HomologicalComplex.homologyMap S.f (k+1)) :=
    mono_homologyMap_telD_of P t hdetH hiso (k+1)
  exact epi_homologyMap_g_of_mono_homologyMap_f hS k hh

/-- **`Hᵏ` of the cokernel projection of `telD` is an epimorphism**, resting only on
`Work.RESOL.mono_sigmaToPi_light` and `Work.RESOL.isIso_sigmaHomologyMap`. -/
theorem epi_homologyMap_cokernel_telD (P : ℕ → Cpx) [HasCoproduct P]
    (t : ∀ n : ℕ, P n ⟶ P (n+1)) (k : ℤ) :
    Epi (HomologicalComplex.homologyMap (cokernel.π (telD P t)) k) :=
  epi_homologyMap_cokernel_telD_of P t (fun k => mono_sigmaToPi_light _)
    (fun k => mono_sigmaToPi_light _) (fun k => isIso_sigmaHomologyMap P k) k

end Work.RESOL.TelDescAux
