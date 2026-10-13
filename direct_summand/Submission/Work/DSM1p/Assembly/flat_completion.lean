import Mathlib
import Submission.Work.DSM1p.Basic
import Submission.Work.DSM1p.Root.flat_closure
import Submission.Work.DSM1p.Root.flat_mod_p_closure
import Submission.Work.DSM1p.Completion.isAdicComplete
import Submission.Work.DSM1p.Completion.torsionFree
import Submission.Work.DSM1p.Root.torsionFree_closure
import Submission.Work.DSM2b.FlatSetup
import Submission.Work.DSM2b.assembly_aux

set_option maxHeartbeats 4000000

/-!
# Flatness of the `p`-adic completion of the root closure `R[a^{1/p^∞}]`

This module proves `Work.DSM1p.Assembly.flat_completion`, the flatness input of Bhatt's
construction (arXiv:1608.08882, Prop. 4.1).  The argument is self-contained apart from the
already-proven pieces of the workspace:

* `flat_mod_pow_completion` : the dévissage `B ⧸ pⁿB` is flat over `R ⧸ pⁿR`, obtained from the
  flatness of the root closure `S = R[a^{1/p^∞}]` (a filtered colimit of free `R`-modules) and the
  canonical identification `B ⧸ pⁿB ≅ S ⧸ pⁿS` (`AdicCompletion.evalₐ`);
* `syzygy_mod_pow` : syzygies modulo `pⁿ` with the Artin–Rees loss;
* `Work.DSM2b.exists_pow_sub_mem_ker_aux` : the elementwise Artin–Rees lemma;
* `Work.DSM2b.flat_of_flat_mod_base_aux` : the assembly of these three inputs into flatness.
-/

namespace Work.DSM1p.Assembly

open Work.DSM1p
open TensorProduct
open scoped TensorProduct

universe u

/-! ## The dévissage for the completion -/

/-- `I ^ n • ⊤ = I ^ n` in the ring itself. -/
lemma smul_top_pow_self {S : Type*} [CommRing S] (I : Ideal S) (n : ℕ) :
    I ^ n • (⊤ : Submodule S S) = I ^ n := by
  rw [Ideal.smul_eq_mul, Ideal.mul_top]

/-- The `n`-th coordinate projection of an adic completion kills exactly `I ^ n`. -/
lemma evalₐ_eq_zero_iff {S : Type*} [CommRing S] (I : Ideal S) (n : ℕ)
    (x : AdicCompletion I S) :
    AdicCompletion.evalₐ I n x = 0 ↔ AdicCompletion.eval I S n x = 0 := by
  have hle : I ^ n ≤ I ^ n • (⊤ : Submodule S S) := le_of_eq (smul_top_pow_self I n).symm
  have hle' : I ^ n • (⊤ : Submodule S S) ≤ I ^ n := le_of_eq (smul_top_pow_self I n)
  have hfac := AdicCompletion.factor_evalₐ_eq_eval (I := I) x hle
  constructor
  · intro h
    rw [h, map_zero] at hfac
    exact hfac.symm
  · intro h
    have hinj : Function.Injective (Ideal.Quotient.factor hle) := by
      rw [RingHom.injective_iff_ker_eq_bot, Ideal.Quotient.factor_ker]
      simpa using Ideal.map_mk_eq_bot_of_le hle'
    rw [h] at hfac
    exact hinj (by rw [hfac, map_zero])

/-- The kernel of the `n`-th coordinate projection is the `n`-th power of the ideal. -/
lemma ker_evalₐ_eq_map {S : Type*} [CommRing S] (I : Ideal S) (hFG : I.FG) (n : ℕ) :
    RingHom.ker (AdicCompletion.evalₐ I n).toRingHom
      = (I ^ n).map (algebraMap S (AdicCompletion I S)) := by
  ext x
  show AdicCompletion.evalₐ I n x = 0 ↔ x ∈ (I ^ n).map (algebraMap S (AdicCompletion I S))
  rw [evalₐ_eq_zero_iff, ← LinearMap.mem_ker,
    ← AdicCompletion.pow_smul_top_eq_ker_eval (M := S) (I := I) hFG, Ideal.smul_top_eq_map]
  rfl

/-- **Dévissage for the completion**: `B ⧸ pⁿB` is flat over `R ⧸ pⁿR`. -/
theorem flat_mod_pow_completion (R : Type*) [CommRing R] (p : ℕ) (hp0 : p ≠ 0) (a : R) (n : ℕ) :
    Module.Flat (R ⧸ Ideal.span {(p : R) ^ n})
      (RootClosureCompletion R p a ⧸
        (Ideal.span {(p : R) ^ n}).map (algebraMap R (RootClosureCompletion R p a))) := by
  haveI : Module.Flat R (RootClosure R p a) := Root.flat_closure R p a hp0
  have hS : Module.Flat (R ⧸ Ideal.span {(p : R) ^ n})
      (RootClosure R p a ⧸ (Ideal.span {(p : R) ^ n}).map (algebraMap R (RootClosure R p a))) :=
    Root.flat_quot_map R (RootClosure R p a) (Ideal.span {(p : R) ^ n})
  have hI : (Ideal.span {(p : R) ^ n}).map (algebraMap R (RootClosure R p a))
      = Ideal.span {(p : RootClosure R p a)} ^ n := by
    rw [Ideal.span_singleton_pow, Ideal.map_span]
    simp
  have hcomp : (algebraMap (RootClosure R p a) (RootClosureCompletion R p a)).comp
        (algebraMap R (RootClosure R p a)) = algebraMap R (RootClosureCompletion R p a) := by
    ext x
    rfl
  have hIB : (Ideal.span {(p : RootClosure R p a)} ^ n).map
        (algebraMap (RootClosure R p a) (RootClosureCompletion R p a))
      = (Ideal.span {(p : R) ^ n}).map (algebraMap R (RootClosureCompletion R p a)) := by
    rw [← hI, Ideal.map_map, hcomp]
  have hFG : (Ideal.span {(p : RootClosure R p a)}).FG := ⟨{(p : RootClosure R p a)}, by simp⟩
  have hker := ker_evalₐ_eq_map (Ideal.span {(p : RootClosure R p a)}) hFG n
  let eB : (RootClosureCompletion R p a ⧸
        (Ideal.span {(p : R) ^ n}).map (algebraMap R (RootClosureCompletion R p a)))
      ≃ₐ[RootClosure R p a]
      (RootClosure R p a ⧸
        (Ideal.span {(p : R) ^ n}).map (algebraMap R (RootClosure R p a))) :=
    (Ideal.quotientEquivAlgOfEq (RootClosure R p a) hIB.symm).trans <|
      (Ideal.quotientEquivAlgOfEq (RootClosure R p a) hker).symm.trans <|
      (Ideal.quotientKerAlgEquivOfSurjective
        (AdicCompletion.surjective_evalₐ (Ideal.span {(p : RootClosure R p a)}) n)).trans <|
      (Ideal.quotientEquivAlgOfEq (RootClosure R p a) hI.symm)
  have e : (RootClosureCompletion R p a ⧸
      (Ideal.span {(p : R) ^ n}).map (algebraMap R (RootClosureCompletion R p a)))
      ≃ₐ[R ⧸ Ideal.span {(p : R) ^ n}]
      (RootClosure R p a ⧸
        (Ideal.span {(p : R) ^ n}).map (algebraMap R (RootClosure R p a))) :=
    { eB.toRingEquiv with
      commutes' := fun x => by
        induction x using Quotient.inductionOn with
        | _ r =>
          show eB.toRingEquiv (algebraMap (R ⧸ Ideal.span {(p : R) ^ n})
              (RootClosureCompletion R p a ⧸
                (Ideal.span {(p : R) ^ n}).map (algebraMap R (RootClosureCompletion R p a)))
              (Ideal.Quotient.mk (Ideal.span {(p : R) ^ n}) r))
            = algebraMap (R ⧸ Ideal.span {(p : R) ^ n})
              (RootClosure R p a ⧸
                (Ideal.span {(p : R) ^ n}).map (algebraMap R (RootClosure R p a)))
              (Ideal.Quotient.mk (Ideal.span {(p : R) ^ n}) r)
          rw [show algebraMap (R ⧸ Ideal.span {(p : R) ^ n})
                (RootClosureCompletion R p a ⧸
                  (Ideal.span {(p : R) ^ n}).map (algebraMap R (RootClosureCompletion R p a)))
                (Ideal.Quotient.mk (Ideal.span {(p : R) ^ n}) r)
              = Ideal.Quotient.mk ((Ideal.span {(p : R) ^ n}).map
                  (algebraMap R (RootClosureCompletion R p a)))
                  (algebraMap R (RootClosureCompletion R p a) r) from Ideal.quotientMap_mk,
            show algebraMap (R ⧸ Ideal.span {(p : R) ^ n})
                (RootClosure R p a ⧸
                  (Ideal.span {(p : R) ^ n}).map (algebraMap R (RootClosure R p a)))
                (Ideal.Quotient.mk (Ideal.span {(p : R) ^ n}) r)
              = Ideal.Quotient.mk ((Ideal.span {(p : R) ^ n}).map
                  (algebraMap R (RootClosure R p a)))
                  (algebraMap R (RootClosure R p a) r) from Ideal.quotientMap_mk]
          change eB.toRingEquiv (Ideal.Quotient.mk ((Ideal.span {(p : R) ^ n}).map
                (algebraMap R (RootClosureCompletion R p a)))
                (algebraMap R (RootClosureCompletion R p a) r))
            = Ideal.Quotient.mk ((Ideal.span {(p : R) ^ n}).map
                (algebraMap R (RootClosure R p a))) (algebraMap R (RootClosure R p a) r)
          dsimp only [eB]
          simp only [AlgEquiv.coe_toRingEquiv, Function.comp_apply,
            AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_symm,
            Ideal.quotientEquivAlgOfEq_mk, Ideal.quotientKerAlgEquivOfSurjective_mk,
            AdicCompletion.evalₐ_of,
            show algebraMap R (RootClosureCompletion R p a) r
              = AdicCompletion.of (Ideal.span {(p : RootClosure R p a)})
                  (RootClosure R p a) (algebraMap R (RootClosure R p a) r) from rfl]
          exact Ideal.quotientEquivAlgOfEq_mk (R₁ := RootClosure R p a) (h := hI.symm)
            (x := algebraMap R (RootClosure R p a) r) }
  haveI := hS
  exact Module.Flat.of_linearEquiv e.toLinearEquiv

/-! ## The syzygy lemma -/

variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]

/-- `piScalarRight` of a `1 ⊗ -` element is `coeffMap`. -/
lemma piScalarRight_one_tmul {k : ℕ} (x : Fin k → R) :
    TensorProduct.piScalarRight R B B (Fin k) ((1 : B) ⊗ₜ[R] x)
      = Work.DSM2b.coeffMap (B := B) x := by
  rw [← Work.DSM2b.piScalarRight_symm_coeffMap (B := B) x]
  exact LinearEquiv.apply_symm_apply _ _

/-- The image of `S ⊗ B → B^k` under the tensor identification lies in the span of `S`. -/
lemma mem_spanBase_of_map_subtype {k : ℕ} (S : Submodule R (Fin k → R)) (t : B ⊗[R] S) :
    TensorProduct.piScalarRight R B B (Fin k)
      (AlgebraTensorModule.map (LinearMap.id : B →ₗ[B] B) S.subtype t)
      ∈ Work.DSM2b.spanBase (B := B) S := by
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y hx hy => rw [map_add, map_add]; exact Submodule.add_mem _ hx hy
  | tmul b s =>
      simp only [AlgebraTensorModule.map_tmul, LinearMap.id_coe, id_eq]
      have hbs : (b ⊗ₜ[R] (S.subtype s) : B ⊗[R] (Fin k → R))
          = b • ((1 : B) ⊗ₜ[R] (S.subtype s)) := by
        simp [TensorProduct.smul_tmul', smul_eq_mul]
      rw [hbs, map_smul, piScalarRight_one_tmul]
      exact Submodule.smul_mem _ b (Submodule.subset_span ⟨(s : Fin k → R), s.2, rfl⟩)

/-- The structure maps `R → S → M` and `R → M` agree on `R ⧸ πⁿ`. -/
lemma algebraMap_comp_eq {π : R} {n : ℕ} (a : R) :
    algebraMap (R ⧸ Ideal.span {π ^ n})
        (B ⧸ (Ideal.span {π ^ n}).map (algebraMap R B))
        (Ideal.Quotient.mk (Ideal.span {π ^ n}) a)
      = Ideal.Quotient.mk ((Ideal.span {π ^ n}).map (algebraMap R B)) (algebraMap R B a) :=
  Ideal.quotientMap_mk

/-- The `R`- and `B`-algebra structures on `B ⧸ πⁿB` agree on `R`. -/
lemma algebraMap_tower {π : R} {n : ℕ} (a : R) :
    algebraMap B (B ⧸ (Ideal.span {π ^ n}).map (algebraMap R B)) (algebraMap R B a)
      = algebraMap R (B ⧸ (Ideal.span {π ^ n}).map (algebraMap R B)) a := by
  show Ideal.Quotient.mk ((Ideal.span {π ^ n}).map (algebraMap R B)) (algebraMap R B a)
    = algebraMap R (B ⧸ (Ideal.span {π ^ n}).map (algebraMap R B)) a
  exact (algebraMap_comp_eq (B := B) (π := π) a).symm

/-- A power of `(π)` in `B ⧸ πⁿB` has preimage in `B` contained in the same power of `(π) ⊆ B`
(as long as the exponent does not exceed `n`). -/
lemma mem_pow_of_algebraMap_mem {π : R} {n j : ℕ} (hjn : j ≤ n) {b : B}
    (hb : algebraMap B (B ⧸ (Ideal.span {π ^ n}).map (algebraMap R B)) b
      ∈ Ideal.span {algebraMap R (B ⧸ (Ideal.span {π ^ n}).map (algebraMap R B)) π} ^ j) :
    b ∈ Ideal.span {algebraMap R B π} ^ j := by
  let M : Type _ := B ⧸ (Ideal.span {π ^ n}).map (algebraMap R B)
  let f : B →+* M := algebraMap B M
  have hsurj : Function.Surjective f := by
    dsimp only [f]
    rw [Ideal.Quotient.algebraMap_eq]
    exact Ideal.Quotient.mk_surjective
  have hker : RingHom.ker f = Ideal.span {algebraMap R B π} ^ n := by
    dsimp only [f]
    rw [Ideal.Quotient.algebraMap_eq]
    ext x
    rw [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem, Ideal.map_span, Set.image_singleton,
      map_pow, ← Ideal.span_singleton_pow]
  have hb' : f b ∈ Ideal.span {f ((algebraMap R B π) ^ j)} := by
    have hgen : algebraMap R M π = f (algebraMap R B π) :=
      (algebraMap_tower (B := B) (π := π) π).symm
    have hsp : Ideal.span {algebraMap R M π} ^ j = Ideal.span {f ((algebraMap R B π) ^ j)} := by
      rw [Ideal.span_singleton_pow, hgen, ← map_pow]
    rw [← hsp]
    exact hb
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hb'
  obtain ⟨y', rfl⟩ := hsurj y
  have h1 : f (y' * (algebraMap R B π) ^ j) = f b := by
    simpa [map_mul, map_pow, mul_comm] using hy.symm
  have h2 : b - y' * (algebraMap R B π) ^ j ∈ Ideal.span {algebraMap R B π} ^ n := by
    have h0 : f (b - y' * (algebraMap R B π) ^ j) = 0 := by rw [map_sub, h1, sub_self]
    have h3 := RingHom.mem_ker.mpr h0
    rwa [hker] at h3
  have h4 : b - y' * (algebraMap R B π) ^ j ∈ Ideal.span {algebraMap R B π} ^ j :=
    Ideal.pow_le_pow_right hjn h2
  have h5 : y' * (algebraMap R B π) ^ j ∈ Ideal.span {algebraMap R B π} ^ j := by
    have hc : (algebraMap R B π) ^ j ∈ Ideal.span {algebraMap R B π} ^ j :=
      Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_singleton _)) j
    have := Submodule.smul_mem (Ideal.span {algebraMap R B π} ^ j) y' hc
    simpa [smul_eq_mul] using this
  have h6 : b = (b - y' * (algebraMap R B π) ^ j) + y' * (algebraMap R B π) ^ j := by abel
  rw [h6]
  exact Ideal.add_mem _ h4 h5

/-- **Syzygies modulo `π ^ n`, with the Artin–Rees loss.** -/
theorem syzygy_mod_pow {R B : Type u} [CommRing R] [CommRing B] [Algebra R B] (π : R) {k m : ℕ}
    (g : (Fin k → R) →ₗ[R] (Fin m → R)) (c : ℕ)
    (hAR : ∀ n (x : Fin k → R), (∀ i, g x i ∈ Ideal.span {π} ^ n) →
      ∃ z : Fin k → R, x - π ^ (n - c) • z ∈ LinearMap.ker g)
    (hflat : ∀ n : ℕ, Module.Flat (R ⧸ Ideal.span {π ^ n})
      (B ⧸ (Ideal.span {π ^ n}).map (algebraMap R B)))
    (n : ℕ) {y : Fin k → B}
    (hy : ∀ i, Work.DSM2b.coordBase g y i ∈ Ideal.span {algebraMap R B π} ^ n) :
    ∃ w : Fin k → B, w ∈ Work.DSM2b.spanBase (LinearMap.ker g) ∧
      ∀ i, (y - w) i ∈ Ideal.span {algebraMap R B π} ^ (n - c) := by
  classical
  have hpow : Ideal.span {algebraMap R B π} ^ n
      = (Ideal.span {π ^ n}).map (algebraMap R B) := by
    rw [Ideal.span_singleton_pow, Ideal.map_span]
    simp
  let q : B →ₐ[R] B ⧸ (Ideal.span {π ^ n}).map (algebraMap R B) :=
    Ideal.Quotient.mkₐ R ((Ideal.span {π ^ n}).map (algebraMap R B))
  have hqz : ∀ i, q (Work.DSM2b.coordBase g y i) = 0 := by
    intro i
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, ← hpow]
    exact hy i
  have hzrel : Work.DSM2b.coordBase g (fun j => q (y j)) = 0 := by
    rw [← Work.DSM2b.map_coordBase q g y]
    exact funext hqz
  let M : Type u := B ⧸ (Ideal.span {π ^ n}).map (algebraMap R B)
  set S : Type u := R ⧸ Ideal.span {π ^ n} with hSdef
  set gS : (Fin k → S) →ₗ[S] (Fin m → S) := Work.DSM2b.coordBase (R := R) (B := S) g with hgSdef
  haveI : Module.Flat S M := hflat n
  have hgS_single : ∀ (j : Fin k) (i : Fin m),
      gS (Pi.single j 1) i = algebraMap R S (g (Pi.single j 1) i) := by
    intro j i
    rw [hgSdef, Work.DSM2b.coordBase_single]
    rfl
  have hcomp : ∀ a : R, algebraMap S (B ⧸ (Ideal.span {π ^ n}).map (algebraMap R B))
      (algebraMap R S a) = algebraMap R (B ⧸ (Ideal.span {π ^ n}).map (algebraMap R B)) a := by
    intro a
    show algebraMap (R ⧸ Ideal.span {π ^ n})
        (B ⧸ (Ideal.span {π ^ n}).map (algebraMap R B))
        (Ideal.Quotient.mk (Ideal.span {π ^ n}) a) = _
    exact algebraMap_comp_eq (B := B) (π := π) a
  have htower : ∀ z : Fin k → M, Work.DSM2b.coordBase (R := S) (B := M) gS z
      = Work.DSM2b.coordBase (R := R) (B := M) g z := by
    intro z
    ext i
    rw [Work.DSM2b.coordBase_apply, Work.DSM2b.coordBase_apply]
    exact Finset.sum_congr rfl fun j _ => by
      rw [hgS_single j i, hcomp (g (Pi.single j 1) i)]
  have hzrelS : Work.DSM2b.coordBase (R := S) (B := M) gS (fun j => q (y j)) = 0 := by
    rw [htower (fun j => q (y j))]
    exact hzrel
  have hexact : Function.Exact (⇑(LinearMap.ker gS).subtype) ⇑gS :=
    LinearMap.exact_subtype_ker_map gS
  have hrange : LinearMap.range ((LinearMap.ker gS).subtype.lTensor M)
      = LinearMap.ker (LinearMap.lTensor M gS) :=
    (LinearMap.exact_iff.mp (Module.Flat.lTensor_exact M
      (f := (LinearMap.ker gS).subtype) (g := gS) hexact)).symm
  have hzker : (TensorProduct.piScalarRight S M M (Fin k)).symm (fun j => q (y j))
      ∈ LinearMap.ker (LinearMap.lTensor M gS) := by
    rw [LinearMap.mem_ker]
    refine (TensorProduct.piScalarRight S M M (Fin m)).injective ?_
    rw [map_zero, Work.DSM2b.piScalarRight_lTensor_coordBase,
      LinearEquiv.apply_symm_apply]
    exact hzrelS
  have hmem : (fun j => q (y j)) ∈ Work.DSM2b.spanBase (B := M) (LinearMap.ker gS) := by
    have h1 : (TensorProduct.piScalarRight S M M (Fin k)).symm (fun j => q (y j))
        ∈ LinearMap.range ((LinearMap.ker gS).subtype.lTensor M) := by
      rw [hrange]
      exact hzker
    obtain ⟨t, ht⟩ := LinearMap.mem_range.mp h1
    rw [← LinearEquiv.apply_symm_apply (TensorProduct.piScalarRight S M M (Fin k))
      (fun j => q (y j)), ← ht]
    exact mem_spanBase_of_map_subtype (LinearMap.ker gS) t
  -- Artin–Rees
  have hcoeff : ∀ v : Fin k → S, v ∈ LinearMap.ker gS →
      ∃ u : Fin k → M, u ∈ Work.DSM2b.spanBase (B := M) (LinearMap.ker g) ∧
        ∃ w : Fin k → M, w ∈ ((Ideal.span {algebraMap R M π} ^ (n - c)) •
            (⊤ : Submodule M (Fin k → M))) ∧
          Work.DSM2b.coeffMap (R := S) (B := M) v = u + w := by
    intro x hx
    choose xt hxt using fun i => Ideal.Quotient.mk_surjective (x i)
    have hx' : Work.DSM2b.coeffMap (B := S) xt = x := by
      ext i
      rw [Work.DSM2b.coeffMap_apply]
      exact hxt i
    have hmem' : ∀ i, g xt i ∈ Ideal.span {π} ^ n := by
      have h0 : Work.DSM2b.coeffMap (B := S) (g xt) = 0 := by
        rw [← Work.DSM2b.coordBase_coeffMap (R := R) (B := S) g xt, hx', ← hgSdef]
        exact hx
      intro i
      have h1 := congrFun h0 i
      rw [Work.DSM2b.coeffMap_apply, Pi.zero_apply] at h1
      have h2 : g xt i ∈ Ideal.span {π ^ n} := Ideal.Quotient.eq_zero_iff_mem.mp h1
      rwa [← Ideal.span_singleton_pow] at h2
    obtain ⟨zr, hzr⟩ := hAR n xt hmem'
    have hcompC : Work.DSM2b.coeffMap (R := S) (B := M)
        (Work.DSM2b.coeffMap (B := S) xt) = Work.DSM2b.coeffMap (B := M) xt := by
      ext i
      rw [Work.DSM2b.coeffMap_apply, Work.DSM2b.coeffMap_apply, Work.DSM2b.coeffMap_apply]
      exact hcomp (xt i)
    have hsplit : Work.DSM2b.coeffMap (B := M) xt
        = Work.DSM2b.coeffMap (B := M) (xt - π ^ (n - c) • zr)
          + Work.DSM2b.coeffMap (B := M) (π ^ (n - c) • zr) := by
      rw [← map_add, sub_add_cancel]
    refine ⟨Work.DSM2b.coeffMap (B := M) (xt - π ^ (n - c) • zr),
      Submodule.subset_span ⟨_, hzr, rfl⟩, Work.DSM2b.coeffMap (B := M) (π ^ (n - c) • zr),
      ?_, ?_⟩
    · rw [map_smul]
      have hsm : (algebraMap R M (π ^ (n - c))) ∈ Ideal.span {algebraMap R M π} ^ (n - c) := by
        rw [map_pow]
        exact Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_singleton _)) (n - c)
      have key : (algebraMap R M (π ^ (n - c))) • Work.DSM2b.coeffMap (B := M) zr
          = (π ^ (n - c)) • Work.DSM2b.coeffMap (B := M) zr := by
        ext i
        simp [Algebra.smul_def, Pi.smul_apply]
      rw [← key]
      exact Submodule.smul_mem_smul hsm
        (Submodule.mem_top : Work.DSM2b.coeffMap (B := M) zr ∈ (⊤ : Submodule M (Fin k → M)))
    · rw [← hsplit, ← hcompC, hx']
  have hspan_le : Work.DSM2b.spanBase (R := S) (B := M) (LinearMap.ker gS) ≤
      Work.DSM2b.spanBase (B := M) (LinearMap.ker g) ⊔
        (Ideal.span {algebraMap R M π} ^ (n - c)) • (⊤ : Submodule M (Fin k → M)) := by
    rw [Work.DSM2b.spanBase, Submodule.span_le]
    rintro y ⟨w₀, hw₀, rfl⟩
    obtain ⟨u, hu, w, hw, huw⟩ := hcoeff w₀ hw₀
    rw [huw]
    exact Submodule.add_mem _ (Submodule.mem_sup_left hu) (Submodule.mem_sup_right hw)
  have hfinal : (fun j => q (y j)) ∈
      Work.DSM2b.spanBase (B := M) (LinearMap.ker g) ⊔
        (Ideal.span {algebraMap R M π} ^ (n - c)) • (⊤ : Submodule M (Fin k → M)) :=
    hspan_le hmem
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hfinal
  -- lift the `spanBase` part back to `B`
  have hlift : ∃ w : Fin k → B, w ∈ Work.DSM2b.spanBase (B := B) (LinearMap.ker g) ∧
      Work.DSM2b.coeffMap (R := B) (B := M) w = u := by
    rw [Work.DSM2b.spanBase] at hu
    refine Submodule.span_induction (p := fun u _ => ∃ w : Fin k → B,
      w ∈ Work.DSM2b.spanBase (B := B) (LinearMap.ker g) ∧
        Work.DSM2b.coeffMap (R := B) (B := M) w = u) ?_ ?_ ?_ ?_ hu
    · rintro u ⟨x, hx, rfl⟩
      refine ⟨Work.DSM2b.coeffMap (R := R) (B := B) x, Submodule.subset_span ⟨x, hx, rfl⟩, ?_⟩
      ext i
      rw [Work.DSM2b.coeffMap_apply, Work.DSM2b.coeffMap_apply, Work.DSM2b.coeffMap_apply,
        algebraMap_tower (B := B) (π := π) (x i)]
    · exact ⟨0, Submodule.zero_mem _, by ext i; simp⟩
    · rintro u v _ _ ⟨w₁, hw₁, h₁⟩ ⟨w₂, hw₂, h₂⟩
      exact ⟨w₁ + w₂, Submodule.add_mem _ hw₁ hw₂, by rw [map_add, h₁, h₂]⟩
    · rintro c u _ ⟨w, hw, hw'⟩
      obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective c
      refine ⟨c' • w, Submodule.smul_mem _ c' hw, ?_⟩
      show Work.DSM2b.coeffMap (R := B) (B := M) (c' • w) = _
      ext i
      have hwi : algebraMap B M (w i) = u i := by
        rw [← Work.DSM2b.coeffMap_apply (B := M)]
        exact congrFun hw' i
      simp only [Work.DSM2b.coeffMap_apply, Pi.smul_apply, smul_eq_mul, map_mul, hwi]
      rw [Ideal.Quotient.algebraMap_eq]
  obtain ⟨w, hw, hwu⟩ := hlift
  refine ⟨w, hw, fun i => ?_⟩
  -- the two sides differ by `v`
  have hcq : Work.DSM2b.coeffMap (R := B) (B := M) y = fun j => q (y j) := by
    ext j
    rw [Work.DSM2b.coeffMap_apply]
    rfl
  have h1 : Work.DSM2b.coeffMap (R := B) (B := M) (y - w) = v := by
    rw [map_sub, hwu, hcq, ← huv]
    simp
  have hcoord : algebraMap B M ((y - w) i)
      ∈ Ideal.span {algebraMap R M π} ^ (n - c) :=
    (Work.DSM2b.mem_smul_top_fin_iff (B := M) (Ideal.span {algebraMap R M π} ^ (n - c))
      (Work.DSM2b.coeffMap (R := B) (B := M) (y - w))).mp (h1 ▸ hv) i
  exact mem_pow_of_algebraMap_mem (B := B) (π := π) (n := n) (j := n - c)
    (Nat.sub_le n c) hcoord

/-! ## The main theorem -/

/-- **Bhatt's flatness criterion, specialised.**  The `p`-adic completion `B` of the root closure
`S = R[a^{1/p^∞}]` is flat over `R`: `p` is a non-zero-divisor on `R` (hypothesis) and on `B`
(`Completion.torsionFree` applied to `Root.torsionFree_closure`), `B` is `p`-adically complete by
construction (`Completion.isAdicComplete`), `B ⧸ pⁿB` is flat over `R ⧸ pⁿR` for every `n`
(`flat_mod_pow_completion`) and the elementwise Artin–Rees lemma
(`Work.DSM2b.exists_pow_sub_mem_ker_aux`) together with `syzygy_mod_pow` supplies the syzygy
control; `Work.DSM2b.flat_of_flat_mod_base_aux` assembles these into flatness. -/
theorem flat_completion (R : Type*) [CommRing R] [IsNoetherianRing R] (p : ℕ) (hp0 : p ≠ 0)
    (hp : IsSMulRegular R p) (a : R) :
    Module.Flat R (Work.DSM1p.RootClosureCompletion R p a) := by
  haveI hcomp : IsAdicComplete
      (Ideal.span {algebraMap R (Work.DSM1p.RootClosureCompletion R p a) p})
      (Work.DSM1p.RootClosureCompletion R p a) := by
    rw [show algebraMap R (Work.DSM1p.RootClosureCompletion R p a) p
        = (p : Work.DSM1p.RootClosureCompletion R p a) from map_natCast _ _]
    exact Work.DSM1p.Completion.isAdicComplete R p a
  have hregS : IsSMulRegular (RootClosure R p a) (p : RootClosure R p a) :=
    Root.torsionFree_closure R p a hp
  have hregB : IsSMulRegular (Work.DSM1p.RootClosureCompletion R p a)
      (algebraMap R (Work.DSM1p.RootClosureCompletion R p a) p) := by
    rw [map_natCast]
    exact Work.DSM1p.Completion.torsionFree R p a hregS
  exact Work.DSM2b.flat_of_flat_mod_base_aux (R := R)
    (B := Work.DSM1p.RootClosureCompletion R p a) (p : R) hregB
    (fun n => flat_mod_pow_completion R p hp0 a n)
    (fun g => Work.DSM2b.exists_pow_sub_mem_ker_aux (p : R) g)
    (fun g c hAR hflat => syzygy_mod_pow (p : R) g c hAR hflat)

end Work.DSM1p.Assembly
