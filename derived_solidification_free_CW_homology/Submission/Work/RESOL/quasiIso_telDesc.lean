/-
AREA RESOL — the map from the telescope of a sequence to a target receiving a compatible cocone
is a quasi-isomorphism as soon as the cocone maps are eventual quasi-isomorphisms.

# Strategy

Let `P : ℕ → Cpx`, `t : ∀ n, P n ⟶ P (n+1)`, `A := ∐ P`, `d := telD P t = 1 - smap` and
`tel P t = mappingCone d`.  For a complex `K` with a compatible cocone `f n : P n ⟶ K`
(i.e. `t n ≫ f (n+1) = f n`) we show that `telDesc P t K f hf : tel P t ⟶ K` is a
quasi-isomorphism, assuming that for every degree `k` the maps `f n` are quasi-isomorphisms at
degree `k` for all large `n`.

* The key point is that `1 - smap` is a *monomorphism* of complexes (its `n`-th coordinate is
  forced by the previous one, starting from the vanishing `0`-th coordinate): `mono_telD`.
* Hence `S := (A --d--> A --cokernel.π d--> W)` is a short exact short complex, and
  Mathlib's `CochainComplex.mappingCone.quasiIso_descShortComplex` shows that the canonical map
  `p := mappingCone.descShortComplex S : tel P t ⟶ W` is a quasi-isomorphism, with
  `inr d ≫ p = cokernel.π d`.
* Since `d ≫ coconeMap P f = 0` there is a (unique) `g : W ⟶ K` with
  `cokernel.π d ≫ g = coconeMap P f`; comparing the two maps out of the mapping cone on the
  `inl`- and `inr`-parts shows `telDesc P t K f hf = p ≫ g`.  So it remains to show that `g` is a
  quasi-isomorphism.
* Fix `k` and let `N` be such that `H^k (f n)` is an isomorphism for all `n ≥ N`.  Put
  `u := H^k (ι_N ≫ π) : H^k (P N) ⟶ H^k W` and `e := H^k (f N) = u ≫ H^k g` (the identity
  `(ι_N ≫ π) ≫ g = f N` is `Sigma_ι_comp_cokernel_π_comp_telCokernelDesc`).  Since `e` is an
  isomorphism, `H^k g` is an epimorphism (`epi_of_epi_fac`) and, setting
  `χ := inv e ≫ u`, we have `χ ≫ H^k g = 𝟙`; so it remains to prove `H^k g ≫ χ = 𝟙`, i.e. that
  `χ` is also a retraction of `H^k g`.

  To this end cancel the epimorphism `σ ≫ H^k π : ∐ₙ H^k (P n) ⟶ H^k W` (where `σ` is the
  AB4-comparison isomorphism `Work.TOOLKIT.sigmaHomologyMap` and `Epi (H^k π)` is
  `epi_homologyMap_cokernel_telD`).  On the `n`-th summand of the coproduct the required identity
  becomes `H^k (f n) ≫ χ = H^k (ι_n ≫ π)`, which is the component computation
  `homologyMap_f_comp_chi`: for `n ≤ N` use `f n = telTrans n N ≫ f N` and the telescoping
  identity `telTrans n N ≫ (ι_N ≫ π) = ι_n ≫ π`; for `N ≤ n` use that the transition maps are
  isomorphisms on `H^k` from `N` on (`isIso_homologyMap_telTrans_of`) and the same telescoping
  identity in the other direction.

The two inputs `Mono (telD P t)` and `Epi (H^k (cokernel.π d))` are supplied by the module
`Submission.Work.RESOL.telDescAux` (namespace `Work.RESOL.TelDescAux`), which reproduces the
proofs of `mono_telD` and `epi_homologyMap_cokernel_telD` on top of the completed
`Work.RESOL.mono_sigmaToPi_light` and `Work.RESOL.isIso_sigmaHomologyMap`; see the header of that
file.  This keeps the present file independent of the files that are being reworked.

-/
import Mathlib
import Submission.Work.RESOL.Telescope
import Submission.Work.RESOL.Instances
import Submission.Work.RESOL.telDescAux
import Submission.Work.RESOL.isIso_sigmaHomologyMap

open CategoryTheory Limits LightProfinite LightCondensed
open _root_.LightCondensed

noncomputable section

attribute [local instance 2000] Sheaf.instHasColimitsOfShape

namespace Work.RESOL

/-! ## The cokernel of `telD` and the factorisation of `telDesc` -/

/-- The short complex `A --telD--> A --cokernel.π--> cokernel telD`. -/
abbrev telShort (P : ℕ → Cpx) [HasCoproduct P] (t : ∀ n : ℕ, P n ⟶ P (n+1)) :
    ShortComplex Cpx :=
  ShortComplex.mk (telD P t) (cokernel.π (telD P t)) (cokernel.condition (telD P t))

/-- The map `cokernel (telD P t) ⟶ K` induced by a compatible cocone `f`. -/
def telCokernelDesc (P : ℕ → Cpx) [HasCoproduct P] (t : ∀ n : ℕ, P n ⟶ P (n+1)) (K : Cpx)
    (f : ∀ n : ℕ, P n ⟶ K)
    (hf : ∀ n : ℕ, CategoryTheory.CategoryStruct.comp (t n) (f (n+1)) = f n) :
    cokernel (telD P t) ⟶ K :=
  cokernel.desc (telD P t) (coconeMap P f) (telD_coconeMap P t f hf)

lemma cokernel_π_telCokernelDesc (P : ℕ → Cpx) [HasCoproduct P]
    (t : ∀ n : ℕ, P n ⟶ P (n+1)) (K : Cpx) (f : ∀ n : ℕ, P n ⟶ K)
    (hf : ∀ n : ℕ, t n ≫ f (n+1) = f n) :
    cokernel.π (telD P t) ≫ telCokernelDesc P t K f hf = coconeMap P f :=
  cokernel.π_desc (telD P t) (coconeMap P f) (telD_coconeMap P t f hf)

/-- `telDesc` factors through the cokernel of `telD`, via the map `telCokernelDesc`. -/
theorem telDesc_eq_descShortComplex_comp (P : ℕ → Cpx) [HasCoproduct P]
    (t : ∀ n : ℕ, P n ⟶ P (n+1)) (K : Cpx) (f : ∀ n : ℕ, P n ⟶ K)
    (hf : ∀ n : ℕ, t n ≫ f (n+1) = f n) :
    telDesc P t K f hf =
      CochainComplex.mappingCone.descShortComplex (telShort P t) ≫
        telCokernelDesc P t K f hf := by
  change CochainComplex.mappingCone.desc (telD P t) 0 (coconeMap P f) (telD_descEq P t K f hf) =
    CochainComplex.mappingCone.descShortComplex (telShort P t) ≫
      telCokernelDesc P t K f hf
  rw [show CochainComplex.mappingCone.descShortComplex (telShort P t) =
      CochainComplex.mappingCone.desc (telD P t) 0 (cokernel.π (telD P t)) (by simp) from rfl]
  apply HomologicalComplex.hom_ext
  intro j
  rw [HomologicalComplex.comp_f]
  refine (CochainComplex.mappingCone.ext_from_iff (telD P t) (j + 1) j (by ring)
      ((CochainComplex.mappingCone.desc (telD P t) 0 (coconeMap P f)
        (telD_descEq P t K f hf)).f j)
      ((CochainComplex.mappingCone.desc (telD P t) 0 (cokernel.π (telD P t)) (by simp)).f j ≫
        (telCokernelDesc P t K f hf).f j)).2 ⟨?_, ?_⟩
  · -- the `inl`-parts: both vanish, as the cochain parameter is `0`
    rw [CochainComplex.mappingCone.inl_v_desc_f]
    rw [← Category.assoc, CochainComplex.mappingCone.inl_v_desc_f]
    simp
  · -- the `inr`-parts: both are `coconeMap P f`
    rw [← Category.assoc]
    simp only [CochainComplex.mappingCone.inr_f_desc_f]
    rw [← HomologicalComplex.comp_f (cokernel.π (telD P t)) (telCokernelDesc P t K f hf) j,
      cokernel_π_telCokernelDesc]

/-! ## The transition maps of the sequence and the telescoping identities -/

/-- The composite of the transition maps from `P n` to `P m` (for `n ≤ m`). -/
noncomputable def telTrans (P : ℕ → Cpx) [HasCoproduct P] (t : ∀ n : ℕ, P n ⟶ P (n+1))
    (n m : ℕ) (h : n ≤ m) : P n ⟶ P m :=
  Nat.leRecOn (C := fun k => P n ⟶ P k) h (fun {k} ih => ih ≫ t k) (𝟙 (P n))

lemma telTrans_self (P : ℕ → Cpx) [HasCoproduct P] (t : ∀ n : ℕ, P n ⟶ P (n+1)) (n : ℕ) :
    telTrans P t n n (le_refl n) = 𝟙 (P n) := by
  unfold telTrans
  rw [Nat.leRecOn_self]

lemma telTrans_succ (P : ℕ → Cpx) [HasCoproduct P] (t : ∀ n : ℕ, P n ⟶ P (n+1))
    {n m : ℕ} (h : n ≤ m) :
    telTrans P t n (m+1) (Nat.le_succ_of_le h) = telTrans P t n m h ≫ t m := by
  unfold telTrans
  rw [Nat.leRecOn_succ]

/-- `telTrans` only depends on the numerical indices, not on the proof of the inequality. -/
lemma telTrans_irrel (P : ℕ → Cpx) [HasCoproduct P] (t : ∀ n : ℕ, P n ⟶ P (n+1))
    {n m : ℕ} (h h' : n ≤ m) : telTrans P t n m h = telTrans P t n m h' :=
  congrArg (fun q : n ≤ m => telTrans P t n m q) (Subsingleton.elim h h')

/-- The cokernel projection of `telD` is invariant under the transition maps. -/
lemma telTrans_comp_ι_π (P : ℕ → Cpx) [HasCoproduct P] (t : ∀ n : ℕ, P n ⟶ P (n+1))
    {n m : ℕ} (h : n ≤ m) :
    telTrans P t n m h ≫ (Sigma.ι P m ≫ cokernel.π (telD P t)) =
      Sigma.ι P n ≫ cokernel.π (telD P t) := by
  have hstep : ∀ j : ℕ, Sigma.ι P j ≫ cokernel.π (telD P t) =
      t j ≫ Sigma.ι P (j+1) ≫ cokernel.π (telD P t) := by
    intro j
    have hzero : telD P t ≫ cokernel.π (telD P t) = 0 := cokernel.condition (telD P t)
    have hsub : smap P t ≫ cokernel.π (telD P t) = cokernel.π (telD P t) := by
      rw [telD, Preadditive.sub_comp, Category.id_comp] at hzero
      exact (sub_eq_zero.mp hzero).symm
    calc Sigma.ι P j ≫ cokernel.π (telD P t)
        = Sigma.ι P j ≫ smap P t ≫ cokernel.π (telD P t) := by
          conv_lhs => rw [← hsub]
      _ = (t j ≫ Sigma.ι P (j+1)) ≫ cokernel.π (telD P t) := by
          rw [← Category.assoc, Sigma_ι_smap]
      _ = t j ≫ Sigma.ι P (j+1) ≫ cokernel.π (telD P t) := Category.assoc _ _ _
  induction h with
  | refl =>
      rw [telTrans_irrel P t _ (le_refl n), telTrans_self, Category.id_comp]
  | step h ih =>
      rw [telTrans_irrel P t _ (Nat.le_succ_of_le h), telTrans_succ P t h]
      rw [Category.assoc, ← hstep _]
      exact ih

/-- The cocone maps are compatible with the transition maps. -/
lemma telTrans_comp_f (P : ℕ → Cpx) [HasCoproduct P] (t : ∀ n : ℕ, P n ⟶ P (n+1))
    (K : Cpx) (f : ∀ n : ℕ, P n ⟶ K) (hf : ∀ n : ℕ, t n ≫ f (n+1) = f n)
    {n m : ℕ} (h : n ≤ m) : telTrans P t n m h ≫ f m = f n := by
  induction h with
  | refl =>
      rw [telTrans_irrel P t _ (le_refl n), telTrans_self, Category.id_comp]
  | step h ih =>
      rw [telTrans_irrel P t _ (Nat.le_succ_of_le h), telTrans_succ P t h, Category.assoc, hf]
      exact ih

/-- The cocone map `f n` factors through `cokernel.π (telD P t)`. -/
lemma Sigma_ι_comp_cokernel_π_comp_telCokernelDesc (P : ℕ → Cpx) [HasCoproduct P]
    (t : ∀ n : ℕ, P n ⟶ P (n+1)) (K : Cpx) (f : ∀ n : ℕ, P n ⟶ K)
    (hf : ∀ n : ℕ, t n ≫ f (n+1) = f n) (n : ℕ) :
    (Sigma.ι P n ≫ cokernel.π (telD P t)) ≫ telCokernelDesc P t K f hf = f n := by
  rw [Category.assoc, cokernel_π_telCokernelDesc, Sigma_ι_coconeMap]

/-! ## The transition maps are isomorphisms on homology from `N` on -/

/-- If `H^k (f n)` is an isomorphism for `n = m` and `n = m+1`, then so is `H^k (t m)`. -/
lemma isIso_homologyMap_t_of (P : ℕ → Cpx) [HasCoproduct P] (t : ∀ n : ℕ, P n ⟶ P (n+1))
    (K : Cpx) (f : ∀ n : ℕ, P n ⟶ K) (hf : ∀ n : ℕ, t n ≫ f (n+1) = f n)
    {k : ℤ} {N : ℕ} (hiso : ∀ n : ℕ, N ≤ n → IsIso (HomologicalComplex.homologyMap (f n) k))
    {m : ℕ} (hm : N ≤ m) : IsIso (HomologicalComplex.homologyMap (t m) k) := by
  haveI hnext : IsIso (HomologicalComplex.homologyMap (f (m+1)) k) :=
    hiso (m+1) (le_trans hm (Nat.le_succ m))
  have hfac : (HomologicalComplex.homologyMap (t m) k :
        HomologicalComplex.homology (P m) k ⟶ HomologicalComplex.homology (P (m+1)) k) ≫
      (HomologicalComplex.homologyMap (f (m+1)) k :
        HomologicalComplex.homology (P (m+1)) k ⟶ HomologicalComplex.homology K k) =
      HomologicalComplex.homologyMap (f m) k := by
    rw [← HomologicalComplex.homologyMap_comp, hf m]
  haveI hcomp : IsIso ((HomologicalComplex.homologyMap (t m) k :
        HomologicalComplex.homology (P m) k ⟶ HomologicalComplex.homology (P (m+1)) k) ≫
      (HomologicalComplex.homologyMap (f (m+1)) k :
        HomologicalComplex.homology (P (m+1)) k ⟶ HomologicalComplex.homology K k)) :=
    hfac ▸ hiso m hm
  exact IsIso.of_isIso_comp_right
    (HomologicalComplex.homologyMap (t m) k :
      HomologicalComplex.homology (P m) k ⟶ HomologicalComplex.homology (P (m+1)) k)
    (HomologicalComplex.homologyMap (f (m+1)) k :
      HomologicalComplex.homology (P (m+1)) k ⟶ HomologicalComplex.homology K k)

/-- If `H^k (f n)` is an isomorphism for all `n ≥ N`, then so is `H^k` of every transition
composite `telTrans n m` with `N ≤ n ≤ m`. -/
lemma isIso_homologyMap_telTrans_of (P : ℕ → Cpx) [HasCoproduct P]
    (t : ∀ n : ℕ, P n ⟶ P (n+1)) (K : Cpx) (f : ∀ n : ℕ, P n ⟶ K)
    (hf : ∀ n : ℕ, t n ≫ f (n+1) = f n) {k : ℤ} {N : ℕ}
    (hiso : ∀ n : ℕ, N ≤ n → IsIso (HomologicalComplex.homologyMap (f n) k)) {n : ℕ}
    (hn : N ≤ n) (m : ℕ) (hm : n ≤ m) :
    IsIso (HomologicalComplex.homologyMap (telTrans P t n m hm) k) := by
  induction hm with
  | refl =>
      rw [telTrans_irrel P t _ (le_refl n), telTrans_self, HomologicalComplex.homologyMap_id]
      infer_instance
  | step hm ih =>
      rw [telTrans_irrel P t _ (Nat.le_succ_of_le hm), telTrans_succ P t hm,
        HomologicalComplex.homologyMap_comp]
      haveI := ih
      haveI := isIso_homologyMap_t_of P t K f hf hiso (le_trans hn hm)
      infer_instance

/-! ## The section of `H^k (telCokernelDesc)` on the summands -/

/-- **The component computation.**  If `H^k (f n)` becomes an isomorphism for all `n ≥ N`, and
`chi` is any section of `H^k g` over `H^k (f N)` (in the sense that `H^k (f N) ≫ chi` is
`H^k (ι_N ≫ π)`), then `H^k (f n) ≫ chi = H^k (ι_n ≫ π)` for every `n`.

This is the slot chase of the telescope: for `n ≤ N` the cocone map `f n` factors through `f N`
along `telTrans n N`, and for `N ≤ n` the transition map `telTrans N n` is an isomorphism on
homology. -/
lemma homologyMap_f_comp_chi (P : ℕ → Cpx) [HasCoproduct P] (t : ∀ n : ℕ, P n ⟶ P (n+1))
    (K : Cpx) (f : ∀ n : ℕ, P n ⟶ K) (hf : ∀ n : ℕ, t n ≫ f (n+1) = f n) {k : ℤ} {N : ℕ}
    (hiso : ∀ n : ℕ, N ≤ n → IsIso (HomologicalComplex.homologyMap (f n) k))
    (chi : HomologicalComplex.homology K k ⟶
      HomologicalComplex.homology (cokernel (telD P t)) k)
    (hchi : HomologicalComplex.homologyMap (f N) k ≫ chi =
      HomologicalComplex.homologyMap (Sigma.ι P N ≫ cokernel.π (telD P t)) k) (n : ℕ) :
    HomologicalComplex.homologyMap (f n) k ≫ chi =
      HomologicalComplex.homologyMap (Sigma.ι P n ≫ cokernel.π (telD P t)) k := by
  by_cases hn : n ≤ N
  · -- `n ≤ N`: use `f n = telTrans n N ≫ f N` and `telTrans n N ≫ (ι_N ≫ π) = ι_n ≫ π`
    have h1 : HomologicalComplex.homologyMap (f n) k =
        HomologicalComplex.homologyMap (telTrans P t n N hn) k ≫
          HomologicalComplex.homologyMap (f N) k := by
      rw [← HomologicalComplex.homologyMap_comp, telTrans_comp_f P t K f hf hn]
    have h2 : HomologicalComplex.homologyMap (Sigma.ι P n ≫ cokernel.π (telD P t)) k =
        HomologicalComplex.homologyMap (telTrans P t n N hn) k ≫
          HomologicalComplex.homologyMap (Sigma.ι P N ≫ cokernel.π (telD P t)) k := by
      rw [← HomologicalComplex.homologyMap_comp, telTrans_comp_ι_π P t hn,
        HomologicalComplex.homologyMap_comp]
    rw [h1, h2,
      show (HomologicalComplex.homologyMap (telTrans P t n N hn) k ≫
            HomologicalComplex.homologyMap (f N) k) ≫ chi =
          HomologicalComplex.homologyMap (telTrans P t n N hn) k ≫
            (HomologicalComplex.homologyMap (f N) k ≫ chi) from Category.assoc ..,
      hchi]
  · -- `N ≤ n`: cancel the isomorphism `H^k (telTrans N n)`
    have hNn : N ≤ n := le_of_lt (not_le.mp hn)
    haveI hIsoN : IsIso (HomologicalComplex.homologyMap (f N) k) := hiso N le_rfl
    haveI hIson : IsIso (HomologicalComplex.homologyMap (f n) k) := hiso n hNn
    haveI hIsoT : IsIso (HomologicalComplex.homologyMap (telTrans P t N n hNn) k) :=
      isIso_homologyMap_telTrans_of P t K f hf hiso le_rfl n hNn
    have hαβ : HomologicalComplex.homologyMap (telTrans P t N n hNn) k ≫
        HomologicalComplex.homologyMap (f n) k = HomologicalComplex.homologyMap (f N) k := by
      rw [← HomologicalComplex.homologyMap_comp, telTrans_comp_f P t K f hf hNn]
    have hu : HomologicalComplex.homologyMap (Sigma.ι P N ≫ cokernel.π (telD P t)) k =
        HomologicalComplex.homologyMap (telTrans P t N n hNn) k ≫
          HomologicalComplex.homologyMap (Sigma.ι P n ≫ cokernel.π (telD P t)) k := by
      rw [← HomologicalComplex.homologyMap_comp, telTrans_comp_ι_π P t hNn,
        HomologicalComplex.homologyMap_comp]
    -- `chi = inv e ≫ ι_N ≫ π`
    have hchi_eq : chi = inv (HomologicalComplex.homologyMap (f N) k) ≫
        HomologicalComplex.homologyMap (Sigma.ι P N ≫ cokernel.π (telD P t)) k := by
      calc chi = 𝟙 _ ≫ chi := (Category.id_comp chi).symm
        _ = (inv (HomologicalComplex.homologyMap (f N) k) ≫
              HomologicalComplex.homologyMap (f N) k) ≫ chi := by rw [IsIso.inv_hom_id]
        _ = inv (HomologicalComplex.homologyMap (f N) k) ≫
              (HomologicalComplex.homologyMap (f N) k ≫ chi) := Category.assoc ..
        _ = inv (HomologicalComplex.homologyMap (f N) k) ≫
              HomologicalComplex.homologyMap (Sigma.ι P N ≫ cokernel.π (telD P t)) k := by
            rw [hchi]
    -- `inv e ≫ telTrans N n = inv (H^k (f n))`
    have hinv : inv (HomologicalComplex.homologyMap (f N) k) ≫
        HomologicalComplex.homologyMap (telTrans P t N n hNn) k =
        inv (HomologicalComplex.homologyMap (f n) k) := by
      have hstep : (inv (HomologicalComplex.homologyMap (f N) k) ≫
          HomologicalComplex.homologyMap (telTrans P t N n hNn) k) ≫
          HomologicalComplex.homologyMap (f n) k = 𝟙 _ := by
        rw [Category.assoc, hαβ, IsIso.inv_hom_id]
      rw [← cancel_mono (HomologicalComplex.homologyMap (f n) k)]
      rw [hstep, IsIso.inv_hom_id]
    rw [hchi_eq, hu,
      show HomologicalComplex.homologyMap (f n) k ≫
            (inv (HomologicalComplex.homologyMap (f N) k) ≫
              (HomologicalComplex.homologyMap (telTrans P t N n hNn) k ≫
                HomologicalComplex.homologyMap (Sigma.ι P n ≫ cokernel.π (telD P t)) k)) =
          (HomologicalComplex.homologyMap (f n) k ≫
            (inv (HomologicalComplex.homologyMap (f N) k) ≫
              HomologicalComplex.homologyMap (telTrans P t N n hNn) k)) ≫
            HomologicalComplex.homologyMap (Sigma.ι P n ≫ cokernel.π (telD P t)) k from
          (Category.assoc ..).symm,
      hinv, IsIso.hom_inv_id, Category.id_comp]

/-! ## The descent map from the cokernel of `telD` to `K` is a quasi-isomorphism -/

/-- **The descent map from the cokernel of `telD` to `K` is a quasi-isomorphism.** -/
theorem quasiIso_telCokernelDesc (P : ℕ → Cpx) [HasCoproduct P]
    (t : ∀ n : ℕ, P n ⟶ P (n+1)) (K : Cpx) (f : ∀ n : ℕ, P n ⟶ K)
    (hf : ∀ n : ℕ, t n ≫ f (n+1) = f n)
    (hev : ∀ k : ℤ, ∃ N : ℕ, ∀ n ≥ N, QuasiIsoAt (f n) k) :
    QuasiIso (telCokernelDesc P t K f hf) := by
  rw [quasiIso_iff]
  intro k
  rw [quasiIsoAt_iff_isIso_homologyMap]
  obtain ⟨N, hN⟩ := hev k
  haveI hIsoN : IsIso (HomologicalComplex.homologyMap (f N) k) :=
    (quasiIsoAt_iff_isIso_homologyMap (f N) k).mp (hN N le_rfl)
  have hiso : ∀ n : ℕ, N ≤ n → IsIso (HomologicalComplex.homologyMap (f n) k) :=
    fun n hn => (quasiIsoAt_iff_isIso_homologyMap (f n) k).mp (hN n hn)
  rw [CategoryTheory.isIso_iff_mono_and_epi]
  refine ⟨?_, ?_⟩
  · -- `H^k (g)` is a monomorphism: produce the two-sided inverse `chi`
    set s := HomologicalComplex.homologyMap (telCokernelDesc P t K f hf) k with hs
    set chi := inv (HomologicalComplex.homologyMap (f N) k) ≫
        HomologicalComplex.homologyMap (Sigma.ι P N ≫ cokernel.π (telD P t)) k with hchi_def
    -- the epimorphism `σ ≫ H^k π` through which we cancel
    haveI hEpiπ : Epi (HomologicalComplex.homologyMap (cokernel.π (telD P t)) k) :=
      TelDescAux.epi_homologyMap_cokernel_telD P t k
    haveI hIsoσ : IsIso (Work.TOOLKIT.sigmaHomologyMap P k) :=
      isIso_sigmaHomologyMap P k
    have hchi_prop : HomologicalComplex.homologyMap (f N) k ≫ chi =
        HomologicalComplex.homologyMap (Sigma.ι P N ≫ cokernel.π (telD P t)) k := by
      rw [hchi_def,
        show HomologicalComplex.homologyMap (f N) k ≫
              (inv (HomologicalComplex.homologyMap (f N) k) ≫
                HomologicalComplex.homologyMap (Sigma.ι P N ≫ cokernel.π (telD P t)) k) =
            (HomologicalComplex.homologyMap (f N) k ≫
              inv (HomologicalComplex.homologyMap (f N) k)) ≫
              HomologicalComplex.homologyMap (Sigma.ι P N ≫ cokernel.π (telD P t)) k from
          (Category.assoc ..).symm,
        IsIso.hom_inv_id, Category.id_comp]
    have hchi_s : chi ≫ s = 𝟙 (HomologicalComplex.homology K k) := by
      rw [hchi_def, hs, Category.assoc, ← HomologicalComplex.homologyMap_comp,
        Sigma_ι_comp_cokernel_π_comp_telCokernelDesc, IsIso.inv_hom_id]
    -- the component identity `H^k (coconeMap P f) ≫ chi = H^k π`
    have hGchi : HomologicalComplex.homologyMap (coconeMap P f) k ≫ chi =
        HomologicalComplex.homologyMap (cokernel.π (telD P t)) k := by
      have hσι : ∀ n : ℕ, Limits.Sigma.ι (fun m : ℕ => (P m).homology k) n ≫
          Work.TOOLKIT.sigmaHomologyMap P k = HomologicalComplex.homologyMap (Sigma.ι P n) k :=
        fun n => by rw [Work.TOOLKIT.sigmaHomologyMap, Limits.Sigma.ι_comp_desc]
      have hιG : ∀ n : ℕ, HomologicalComplex.homologyMap (Sigma.ι P n) k ≫
          HomologicalComplex.homologyMap (coconeMap P f) k =
          HomologicalComplex.homologyMap (f n) k :=
        fun n => by rw [← HomologicalComplex.homologyMap_comp, Sigma_ι_coconeMap]
      have hιπ : ∀ n : ℕ,
          HomologicalComplex.homologyMap (Sigma.ι P n ≫ cokernel.π (telD P t)) k =
            (Limits.Sigma.ι (fun m : ℕ => (P m).homology k) n ≫
              Work.TOOLKIT.sigmaHomologyMap P k) ≫
              HomologicalComplex.homologyMap (cokernel.π (telD P t)) k :=
        fun n => by rw [hσι n, ← HomologicalComplex.homologyMap_comp]
      rw [← cancel_epi (Work.TOOLKIT.sigmaHomologyMap P k)]
      apply Limits.Sigma.hom_ext
      intro n
      calc Limits.Sigma.ι (fun m : ℕ => (P m).homology k) n ≫
            (Work.TOOLKIT.sigmaHomologyMap P k ≫
              (HomologicalComplex.homologyMap (coconeMap P f) k ≫ chi))
          = (Limits.Sigma.ι (fun m : ℕ => (P m).homology k) n ≫
              Work.TOOLKIT.sigmaHomologyMap P k) ≫
              (HomologicalComplex.homologyMap (coconeMap P f) k ≫ chi) := by
            simp only [Category.assoc]
        _ = (HomologicalComplex.homologyMap (Sigma.ι P n) k ≫
              HomologicalComplex.homologyMap (coconeMap P f) k) ≫ chi := by
            rw [hσι n]
            simp only [Category.assoc]
        _ = HomologicalComplex.homologyMap (f n) k ≫ chi := by
            rw [hιG n]
        _ = HomologicalComplex.homologyMap (Sigma.ι P n ≫ cokernel.π (telD P t)) k :=
            homologyMap_f_comp_chi P t K f hf hiso chi hchi_prop n
        _ = (Limits.Sigma.ι (fun m : ℕ => (P m).homology k) n ≫
              Work.TOOLKIT.sigmaHomologyMap P k) ≫
              HomologicalComplex.homologyMap (cokernel.π (telD P t)) k := hιπ n
        _ = Limits.Sigma.ι (fun m : ℕ => (P m).homology k) n ≫
              (Work.TOOLKIT.sigmaHomologyMap P k ≫
                HomologicalComplex.homologyMap (cokernel.π (telD P t)) k) := by
            simp only [Category.assoc]
    -- `s ≫ chi = 𝟙`, by cancelling the epimorphism `H^k π`
    have hs_chi : s ≫ chi = 𝟙 (HomologicalComplex.homology (cokernel (telD P t)) k) := by
      have hπs : HomologicalComplex.homologyMap (cokernel.π (telD P t)) k ≫ s =
          HomologicalComplex.homologyMap (coconeMap P f) k := by
        rw [hs, ← HomologicalComplex.homologyMap_comp, cokernel_π_telCokernelDesc]
      rw [← cancel_epi (HomologicalComplex.homologyMap (cokernel.π (telD P t)) k)]
      rw [show HomologicalComplex.homologyMap (cokernel.π (telD P t)) k ≫ (s ≫ chi) =
            (HomologicalComplex.homologyMap (cokernel.π (telD P t)) k ≫ s) ≫ chi from
          (Category.assoc ..).symm,
        hπs, hGchi, Category.comp_id]
    haveI : IsIso s := IsIso.mk ⟨chi, hs_chi, hchi_s⟩
    exact inferInstance
  · -- surjectivity: `H^k (f N)` factors as `H^k (ι_N ≫ π) ≫ H^k g` and is an isomorphism
    haveI : Epi (HomologicalComplex.homologyMap (f N) k) := inferInstance
    refine CategoryTheory.epi_of_epi_fac (f := HomologicalComplex.homologyMap
        (Sigma.ι P N ≫ cokernel.π (telD P t)) k)
      (g := HomologicalComplex.homologyMap (telCokernelDesc P t K f hf) k)
      (h := HomologicalComplex.homologyMap (f N) k) ?_
    rw [← HomologicalComplex.homologyMap_comp,
      Sigma_ι_comp_cokernel_π_comp_telCokernelDesc]

theorem quasiIso_telDesc (P : ℕ → Work.RESOL.Cpx) [CategoryTheory.Limits.HasCoproduct P]
    (t : ∀ n : ℕ, P n ⟶ P (n+1)) (K : Work.RESOL.Cpx) (f : ∀ n : ℕ, P n ⟶ K)
    (hf : ∀ n : ℕ, CategoryTheory.CategoryStruct.comp (t n) (f (n+1)) = f n)
    (hev : ∀ k : ℤ, ∃ N : ℕ, ∀ n ≥ N, QuasiIsoAt (f n) k) :
    QuasiIso (Work.RESOL.telDesc P t K f hf) := by
  haveI hmono : Mono (telD P t) := TelDescAux.mono_telD P t
  have hS : (telShort P t).ShortExact :=
    ShortComplex.ShortExact.mk'
      (ShortComplex.exact_of_g_is_cokernel _
        (cokernelIsCokernel (telD P t))) hmono inferInstance
  haveI hp : QuasiIso (CochainComplex.mappingCone.descShortComplex (telShort P t)) :=
    CochainComplex.mappingCone.quasiIso_descShortComplex hS
  haveI hg : QuasiIso (telCokernelDesc P t K f hf) := quasiIso_telCokernelDesc P t K f hf hev
  rw [telDesc_eq_descShortComplex_comp P t K f hf]
  exact quasiIso_comp (CochainComplex.mappingCone.descShortComplex (telShort P t))
    (telCokernelDesc P t K f hf)

end Work.RESOL
