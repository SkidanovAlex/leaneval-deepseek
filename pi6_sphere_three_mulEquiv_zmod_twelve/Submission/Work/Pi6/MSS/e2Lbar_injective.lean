import Mathlib
import Submission.Work.Pi6.MSS.e2Lbar
import Submission.Work.Pi6.MSS.evZ_transpose
import Submission.Work.Pi6.MSS.evS_bij
import Submission.Work.Pi6.MSS.evSaux
import Submission.Work.Pi6.MSS.evZkerle_proof
import Submission.Work.Pi6.MSS.pagesData
import Submission.Work.Pi6.MSS.e2L0_imd
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# Injectivity of the second-page pairing `E_2^{s,q} → (ker d¹)^*`

`Work.Pi6.MSS.e2Lbar` is the descent to the second page of the pairing `e2L0` on representatives,
`e2L0 x v = evZ x (e2Hb v)` (`x ∈ Z_2^s`, `v` a `d¹`-cycle of `E¹_{s,q}`).  Here we prove that this
descent is **injective**: if `x ∈ Z_2^s` pairs to zero with every `d¹`-cycle of `E¹_{s,q}`, then `x`
lies in the denominator `pDen 2 s (s+q)`, i.e. its class in `E_2^{s,q}` vanishes.

The argument is the duality of the first page: `evZ : Z_1^{s,q} ⟶ (E¹_{s,q})^*` is surjective over a
field (`Work.Pi6.MSS.evZsurj`) and its kernel is the denominator of `E_1^s`
(`Work.Pi6.MSS.evZkerle_proof`), while the cohomological coboundary `δ` is the transpose of the
homological differential `d¹` (`Work.Pi6.MSS.evZ_transpose`).

* `x ∈ Z_2^{t+1}` pairing to zero means `Φ := (evZ x) ∘ e2Hb` kills `ker d¹`.
* Over a field `Φ = χ ∘ d¹` for some `χ` (`Work.Pi6.MSS.exists_comp_of_ker_le`), and `χ` is `evZ y`
  for a cycle `y ∈ Z_1^t` (`evZsurj`).
* The transpose relation then gives `evZ x = evZ (δy)`, so that `x - δy ∈ pDen 1`
  (`evZkerle_proof`).
* The filtration algebra (`mem_pDen_two_of_sub_mem_pDen_one`) upgrades this to `x ∈ pDen 2`:
  `δy ∈ B_2 ⊆ pDen 2` and the `F^{t+2}`-part of `x - δy` is a `Z_1^{t+2}`-cycle.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Pi6.MSS

noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-! ## Transport of `pB` along equalities of the degree -/

/-- Membership in `pB` is invariant under the transport of the degree. -/
theorem pd_xcast_mem_pB_iff {𝕜 : Type} [Field 𝕜] {W : CohFilt 𝕜} {r s a b : ℕ}
    (h : a = b) (x : W.C.X a) :
    W.xcast h x ∈ pB 𝕜 W r s b ↔ x ∈ pB 𝕜 W r s a := by
  cases h
  simp only [CohFilt.xcast_rfl, LinearMap.id_apply]

/-- `evS` on the class of a cycle is `evZ` on the cycle. -/
theorem evS_mkQ (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (s n : ℕ) (x : ↥(pZ 𝕜 (Wc 𝕜 p) 1 s n)) :
    evS 𝕜 p s n (hannSerre 𝕜 p)
      (Submodule.mkQ ((pDen 𝕜 (Wc 𝕜 p) 1 s n).comap (pZ 𝕜 (Wc 𝕜 p) 1 s n).subtype) x)
      = evZ 𝕜 p s n (hannSerre 𝕜 p) x := by
  rw [evS]
  exact Submodule.liftQ_apply _ _ _

/-! ## The filtration algebra: `x - z ∈ pDen 1` with `z ∈ pB 2` forces `x ∈ pDen 2` -/

/-- **The filtration step.**  If `x ∈ Z_2^s` and `x - z ∈ pDen 1 s n` for a `z ∈ B_2^s`, then
`x ∈ pDen 2 s n`.  Indeed, writing `x - z = a + b` with `a ∈ F^{s+1}` and `b ∈ B_1^s ⊆ B_2^s`, the
element `a` is a `Z_1^{s+1}`-cycle (`δa = δx - δz - δb = δx ∈ F^{s+2}`), while
`x = z + a + b ∈ Z_1^{s+1} ⊔ B_2^s = pDen 2 s n`. -/
theorem mem_pDen_two_of_sub_mem_pDen_one {𝕜 : Type} [Field 𝕜] (W : CohFilt 𝕜) (s n : ℕ)
    (x : ↥(pZ 𝕜 W 2 s n)) (z : W.C.X n)
    (hz : z ∈ pB 𝕜 W 2 s n) (hxz : (x : W.C.X n) - z ∈ pDen 𝕜 W 1 s n) :
    (x : W.C.X n) ∈ pDen 𝕜 W 2 s n := by
  rw [pDen_one_eq] at hxz
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hxz
  have hb1 : b ∈ pB 𝕜 W 1 s n := by
    rw [pB_one_eq]; exact hb
  have hb2 : b ∈ pB 𝕜 W 2 s n := pd_pB_mono (by norm_num) hb1
  have hxab : (x : W.C.X n) = a + b + z := by rw [hab]; abel
  have h1 : W.d n (x : W.C.X n) = W.d n a + W.d n b := by
    rw [hxab, map_add, map_add, pd_pB_leib 2 s n z hz, add_zero]
  have hda : W.d n a = W.d n (x : W.C.X n) := by rw [h1, pd_pB_leib 1 s n b hb1, add_zero]
  have haZ : a ∈ pZ 𝕜 W 1 (s+1) n :=
    (mem_pZ_one W (s+1) n a).mpr ⟨ha, by rw [hda]; exact x.2.2⟩
  have hsum : (x : W.C.X n) = z + a + b := by rw [hxab]; abel
  rw [hsum]
  exact Submodule.mem_sup.mpr ⟨a, haZ, z + b, Submodule.add_mem _ hz hb2, by abel⟩

/-! ## The analytic step -/

/-- **The analytic step.**  If `x ∈ Z_2^{t+1}` pairs to zero (via `e2L0`) with the `d¹`-cycles of
`E¹_{t+1,q}`, then `x` differs from an explicit `B_2^{t+1}`-element `δy`, `y ∈ Z_1^t`, by an
element of `pDen 1 t+1`.

The proof transposes the first differential: `Φ := (evZ x) ∘ e2Hb` kills `ker d¹`, hence factors as
`χ ∘ d¹`; surjectivity of `evZ` realises `χ` as `evZ y`, and the transpose relation
`evZ (δy) = (evZ y) ∘ d¹` identifies `evZ x` with `evZ (δy)`, so that `x - δy` lies in the kernel of
`evZ`, i.e. in `pDen 1`. -/
theorem e2L0_sub_delta_mem_pDen_one {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (t q : ℕ)
    (x : ↥(pZ 𝕜 (Wc 𝕜 p) 2 (t+1) ((t+1)+q)))
    (hx : e2L0 𝕜 E B p (t+1) q x = 0) :
    ∃ y : ↥(pZ 𝕜 (Wc 𝕜 p) 1 t (t+q)),
      (x : (Wc 𝕜 p).C.X ((t+1)+q))
        - (Wc 𝕜 p).xcast (show (t+q)+1 = (t+1)+q by omega)
            ((Wc 𝕜 p).d (t+q) (y : (Wc 𝕜 p).C.X (t+q)))
        ∈ pDen 𝕜 (Wc 𝕜 p) 1 (t+1) ((t+1)+q) := by
  let x' : ↥(pZ 𝕜 (Wc 𝕜 p) 1 (t+1) ((t+1)+q)) :=
    ⟨(x : (Wc 𝕜 p).C.X ((t+1)+q)), pZ_two_le_one 𝕜 p (t+1) ((t+1)+q) x.2⟩
  let D : (Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q).X (t+1) →ₗ[𝕜]
      (Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q).X t :=
    ((Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q).d (t+1) t).hom
  let Hb := e2Hb 𝕜 (Kg 𝕜 p (t+1)) ((t+1)+q)
  let φ : (↥(Work.StemsB.fdZ 𝕜 (Kg 𝕜 p (t+1)) ((t+1)+q)) ⧸
      Work.StemsB.fdH 𝕜 (Kg 𝕜 p (t+1)) ((t+1)+q)) →ₗ[𝕜] 𝕜 :=
    evZ 𝕜 p (t+1) ((t+1)+q) (hannSerre 𝕜 p) x'
  let Φ : (Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q).X (t+1) →ₗ[𝕜] 𝕜 :=
    φ.comp Hb.hom.hom
  have hkerle : LinearMap.ker D ≤ LinearMap.ker Φ := by
    intro v hv
    rw [LinearMap.mem_ker]
    have hv' : v ∈ e2KerD 𝕜 p (t+1) q := hv
    have h0 := LinearMap.congr_fun hx ⟨v, hv'⟩
    rw [e2L0_evZ_apply 𝕜 p (t+1) q x ⟨v, hv'⟩] at h0
    exact h0
  obtain ⟨χ, hχ⟩ := exists_comp_of_ker_le D Φ hkerle
  let Hb' := e2Hb 𝕜 (Kg 𝕜 p t) (t+q)
  let χ' : (↥(Work.StemsB.fdZ 𝕜 (Kg 𝕜 p t) (t+q)) ⧸
      Work.StemsB.fdH 𝕜 (Kg 𝕜 p t) (t+q)) →ₗ[𝕜] 𝕜 :=
    χ.comp Hb'.inv.hom
  obtain ⟨y, hyχ⟩ := evZsurj 𝕜 E B p t (t+q) (hannSerre 𝕜 p) χ'
  refine ⟨y, ?_⟩
  have hd : (t+q)+1 = (t+1)+q := by omega
  have hdy : (Wc 𝕜 p).d (t+q) (y : (Wc 𝕜 p).C.X (t+q))
      ∈ pZ 𝕜 (Wc 𝕜 p) 1 (t+1) ((t+q)+1) := by
    refine (mem_pZ_one (Wc 𝕜 p) (t+1) ((t+q)+1) _).mpr ⟨y.2.2, ?_⟩
    rw [pd_d_comp_d_apply]
    exact Submodule.zero_mem _
  let z : (Wc 𝕜 p).C.X ((t+1)+q) :=
    (Wc 𝕜 p).xcast hd ((Wc 𝕜 p).d (t+q) (y : (Wc 𝕜 p).C.X (t+q)))
  let ze : ↥(pZ 𝕜 (Wc 𝕜 p) 1 (t+1) ((t+1)+q)) := ⟨z, pd_pZ_xcast rfl hd hdy⟩
  have hyZ : (ze : (Wc 𝕜 p).C.X ((t+1)+q))
      = (Wc 𝕜 p).xcast (show (t+q)+1 = (t+1)+q by omega)
          ((Wc 𝕜 p).d (t+q) (y : (Wc 𝕜 p).C.X (t+q))) := by
    show (Wc 𝕜 p).xcast hd _ = _
    exact pd_xcast_congr hd _ _
  have heq : evZ 𝕜 p (t+1) ((t+1)+q) (hannSerre 𝕜 p) x' =
      evZ 𝕜 p (t+1) ((t+1)+q) (hannSerre 𝕜 p) ze := by
    apply LinearMap.ext
    intro wq
    obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective
      (Work.StemsB.fdH 𝕜 (Kg 𝕜 p (t+1)) ((t+1)+q)) wq
    have hL : (evZ 𝕜 p (t+1) ((t+1)+q) (hannSerre 𝕜 p) x')
        ((Work.StemsB.fdH 𝕜 (Kg 𝕜 p (t+1)) ((t+1)+q)).mkQ w)
        = χ (D (e1elt 𝕜 p (t+1) q w)) := by
      show φ ((Work.StemsB.fdH 𝕜 (Kg 𝕜 p (t+1)) ((t+1)+q)).mkQ w)
        = χ (D (e1elt 𝕜 p (t+1) q w))
      have h1 : φ ((Work.StemsB.fdH 𝕜 (Kg 𝕜 p (t+1)) ((t+1)+q)).mkQ w)
          = Φ (e1elt 𝕜 p (t+1) q w) := by
        show φ ((Work.StemsB.fdH 𝕜 (Kg 𝕜 p (t+1)) ((t+1)+q)).mkQ w)
          = φ (Hb.hom.hom (e1elt 𝕜 p (t+1) q w))
        congr 1
        rw [e1elt]
        exact (Iso.inv_hom_id_apply Hb _).symm
      rw [h1, ← hχ]
      rfl
    have hR : (evZ 𝕜 p (t+1) ((t+1)+q) (hannSerre 𝕜 p) ze)
        ((Work.StemsB.fdH 𝕜 (Kg 𝕜 p (t+1)) ((t+1)+q)).mkQ w)
        = χ (D (e1elt 𝕜 p (t+1) q w)) := by
      rw [evZ_transpose 𝕜 E B p t q y ze hyZ w]
      rw [evS_mkQ 𝕜 E B p t (t+q) y, hyχ]
      show χ (Hb'.inv.hom (d1elt 𝕜 p t q w)) = χ (D (e1elt 𝕜 p (t+1) q w))
      congr 1
      rw [d1elt]
      exact Iso.hom_inv_id_apply Hb' _
    rw [hL, hR]
  have hzero : evZ 𝕜 p (t+1) ((t+1)+q) (hannSerre 𝕜 p) (x' - ze) = 0 := by
    rw [map_sub, heq, sub_self]
  have hmem : ((x' - ze : ↥(pZ 𝕜 (Wc 𝕜 p) 1 (t+1) ((t+1)+q))) :
      (Wc 𝕜 p).C.X ((t+1)+q)) ∈ pDen 𝕜 (Wc 𝕜 p) 1 (t+1) ((t+1)+q) :=
    evZkerle_proof 𝕜 E B p (t+1) ((t+1)+q) (hannSerre 𝕜 p) (LinearMap.mem_ker.mpr hzero)
  have hconv : (x : (Wc 𝕜 p).C.X ((t+1)+q)) - z ∈ pDen 𝕜 (Wc 𝕜 p) 1 (t+1) ((t+1)+q) := by
    simpa only [ze, x', Submodule.coe_sub, Submodule.coe_subtype] using hmem
  rw [show (Wc 𝕜 p).xcast (show (t+q)+1 = (t+1)+q by omega)
      ((Wc 𝕜 p).d (t+q) (y : (Wc 𝕜 p).C.X (t+q))) = z from by
    show (Wc 𝕜 p).xcast hd _ = z
    rfl]
  exact hconv

/-! ## The main theorem -/

theorem e2Lbar_injective (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (s q : ℕ) :
    Function.Injective (Work.Pi6.MSS.e2Lbar 𝕜 E B p s q) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro y hy
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective
    ((pDen 𝕜 (Wc 𝕜 p) 2 s (s+q)).comap (pZ 𝕜 (Wc 𝕜 p) 2 s (s+q)).subtype) y
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  have hy0 : e2L0 𝕜 E B p s q x = 0 := by
    rw [← e2Lbar_mkQ]
    simpa only [LinearMap.mem_ker] using hy
  have hmem : (x : (Wc 𝕜 p).C.X (s+q)) ∈ pDen 𝕜 (Wc 𝕜 p) 2 s (s+q) := by
    match s with
    | 0 =>
      let x' : ↥(pZ 𝕜 (Wc 𝕜 p) 1 0 (0+q)) :=
        ⟨(x : (Wc 𝕜 p).C.X (0+q)), pZ_two_le_one 𝕜 p 0 (0+q) x.2⟩
      have hd0 : ((Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q).d 0 (0-1)) = 0 :=
        HomologicalComplex.shape _ 0 0 (by simp [ComplexShape.down])
      have hφ : evZ 𝕜 p 0 (0+q) (hannSerre 𝕜 p) x' = 0 := by
        apply LinearMap.ext
        intro wq
        obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective
          (Work.StemsB.fdH 𝕜 (Kg 𝕜 p 0) (0+q)) wq
        have hv : ((e2Hb 𝕜 (Kg 𝕜 p 0) (0+q)).inv.hom
            ((Work.StemsB.fdH 𝕜 (Kg 𝕜 p 0) (0+q)).mkQ w)) ∈ e2KerD 𝕜 p 0 q := by
          rw [show e2KerD 𝕜 p 0 q
              = LinearMap.ker (((Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q).d 0 (0-1)).hom)
              from rfl, hd0, ModuleCat.hom_zero, LinearMap.ker_zero]
          exact Submodule.mem_top
        have hkey := LinearMap.congr_fun hy0
          (⟨(e2Hb 𝕜 (Kg 𝕜 p 0) (0+q)).inv.hom
            ((Work.StemsB.fdH 𝕜 (Kg 𝕜 p 0) (0+q)).mkQ w), hv⟩ : ↥(e2KerD 𝕜 p 0 q))
        rw [e2L0_evZ_apply 𝕜 p 0 q x _] at hkey
        rw [Iso.inv_hom_id_apply] at hkey
        exact hkey
      have hmem1 : (x : (Wc 𝕜 p).C.X (0+q)) ∈ pDen 𝕜 (Wc 𝕜 p) 1 0 (0+q) :=
        evZkerle_proof 𝕜 E B p 0 (0+q) (hannSerre 𝕜 p) (LinearMap.mem_ker.mpr hφ)
      exact mem_pDen_two_of_sub_mem_pDen_one (Wc 𝕜 p) 0 (0+q) x 0 (Submodule.zero_mem _)
        (by simpa using hmem1)
    | (t+1) =>
      obtain ⟨y, hyx⟩ := e2L0_sub_delta_mem_pDen_one 𝕜 p t q x hy0
      have hd : (t+q)+1 = (t+1)+q := by omega
      have hdy : (Wc 𝕜 p).d (t+q) (y : (Wc 𝕜 p).C.X (t+q))
          ∈ pB 𝕜 (Wc 𝕜 p) 2 (t+1) ((t+q)+1) := by
        refine (pd_mem_pB_succ (r := 2) (s := t+1) (n := t+q) (z := _)).mpr ⟨y.2.2, y, ?_, rfl⟩
        show (y : (Wc 𝕜 p).C.X (t+q)) ∈ (Wc 𝕜 p).F (t+1+1-2) (t+q)
        rw [show t+1+1-2 = t by omega]
        exact y.2.1
      have hz : (Wc 𝕜 p).xcast hd ((Wc 𝕜 p).d (t+q) (y : (Wc 𝕜 p).C.X (t+q)))
          ∈ pB 𝕜 (Wc 𝕜 p) 2 (t+1) ((t+1)+q) :=
        (pd_xcast_mem_pB_iff hd _).mpr hdy
      refine mem_pDen_two_of_sub_mem_pDen_one (Wc 𝕜 p) (t+1) ((t+1)+q) x _ hz ?_
      rw [show (Wc 𝕜 p).xcast (show (t+q)+1 = (t+1)+q by omega)
          ((Wc 𝕜 p).d (t+q) (y : (Wc 𝕜 p).C.X (t+q))) = (Wc 𝕜 p).xcast hd _ from
        pd_xcast_congr _ hd _]
      exact hyx
  exact Submodule.mem_comap.mpr hmem

end

end Work.Pi6.MSS
