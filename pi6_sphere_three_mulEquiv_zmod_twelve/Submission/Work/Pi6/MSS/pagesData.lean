import Mathlib
import Submission.Work.Pi6.MSS.PageData
import Submission.Work.Pi6.MSS.Pages

/-! # The pages of a filtered cochain complex with a product -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits
open Classical
attribute [local instance] Classical.propDecidable

noncomputable section

variable {𝕜 : Type} [Field 𝕜] {W : CohFilt 𝕜}

/-! ## 1. Elementary facts about the filtered complex -/

theorem pd_d_comp_d_apply (n : ℕ) (z : W.C.X n) : W.d (n+1) (W.d n z) = 0 := by
  have h0 := congrArg (fun f : W.C.X n ⟶ W.C.X (n+2) => f.hom z)
    (HomologicalComplex.d_comp_d W.C n (n+1) (n+2))
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply, CohFilt.d] using h0

theorem pd_F_mono_of_le {a b n : ℕ} (h : a ≤ b) : W.F b n ≤ W.F a n := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact le_trans (W.F_mono _ n) ih

theorem pd_transport_mem {t a b : ℕ} (h : a = b) {x : W.C.X a} (hx : x ∈ W.F t a) :
    (CategoryTheory.eqToHom (congrArg (fun t => W.C.X t) h)).hom x ∈ W.F t b := by
  cases h
  simpa only [CategoryTheory.eqToHom_refl, ModuleCat.hom_id, LinearMap.id_apply] using hx

theorem pd_dPrev_zero : W.dPrev 0 = 0 := by
  have h : W.C.d (0-1) 0 = 0 :=
    W.C.shape (0-1) 0 (by simp only [ComplexShape.up_Rel]; omega)
  rw [CohFilt.dPrev, h]
  exact ModuleCat.hom_zero

/-! ## 2. The cycles -/

theorem pd_pZ_leib (r s n : ℕ) (x : ↥(pZ 𝕜 W r s n)) :
    W.d n (x : W.C.X n) ∈ pZ 𝕜 W r (s + r) (n + 1) := by
  refine ⟨x.2.2, ?_⟩
  show W.d (n+1) (W.d n (x : W.C.X n)) ∈ W.F ((s + r) + r) (n + 1 + 1)
  rw [pd_d_comp_d_apply]
  exact Submodule.zero_mem _

theorem pd_pZmap_apply (r s n : ℕ) (x : ↥(pZ 𝕜 W r s n)) :
    (pZmap 𝕜 W r s n x : W.C.X (n + 1)) = W.d n (x : W.C.X n) := by
  have hz : ∀ y : ↥(pZ 𝕜 W r s n), W.d n (y : W.C.X n) ∈ pZ 𝕜 W r (s + r) (n + 1) :=
    fun y => pd_pZ_leib r s n y
  unfold pZmap
  rw [dif_pos hz]
  rfl

theorem pd_pZ_anti {r r' s s' n : ℕ} (h₁ : r ≤ r') (h₂ : s ≤ s') :
    pZ 𝕜 W r' s' n ≤ pZ 𝕜 W r s n := by
  intro x hx
  refine ⟨pd_F_mono_of_le h₂ hx.1, ?_⟩
  show W.d n x ∈ W.F (s + r) (n+1)
  exact pd_F_mono_of_le (by omega) hx.2

/-! ## 3. The boundaries -/

theorem pd_pB_leib (r s n : ℕ) (x : W.C.X n) (hx : x ∈ pB 𝕜 W r s n) : W.d n x = 0 := by
  obtain ⟨w, hw, hwx⟩ := hx.2
  rw [← hwx]
  have h0 := congrArg (fun f : W.C.X (n-1) ⟶ W.C.X (n+1) => f.hom w)
    (HomologicalComplex.d_comp_d W.C (n-1) n (n+1))
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply, CohFilt.d, CohFilt.dPrev] using h0

theorem pd_pB_mono {r r' s n : ℕ} (h : r ≤ r') : pB 𝕜 W r s n ≤ pB 𝕜 W r' s n := by
  intro x hx
  obtain ⟨w, hw, hwx⟩ := hx.2
  refine ⟨hx.1, w, pd_F_mono_of_le (by omega) hw, hwx⟩

theorem pd_pB_zero (r s : ℕ) : pB 𝕜 W r s 0 = ⊥ := by
  have hd : W.dPrev 0 = 0 := pd_dPrev_zero (W := W)
  rw [pB, hd]
  simp

theorem pd_pB_le_F_succ (r s m : ℕ) : pB 𝕜 W r s (m+1) ≤ W.F (s + 1 - r) (m+1) := by
  intro x hx
  obtain ⟨w, hw, hwx⟩ := hx.2
  rw [← hwx]
  exact W.F_leib (s + 1 - r) m w hw

theorem pd_pB_le_F (r s n : ℕ) : pB 𝕜 W r s n ≤ W.F (s + 1 - r) n := by
  cases n with
  | zero => rw [pd_pB_zero]; exact bot_le
  | succ m => exact pd_pB_le_F_succ r s m

theorem pd_pB_le_pDen (r s n : ℕ) : pB 𝕜 W r s n ≤ pDen 𝕜 W r s n :=
  le_sup_right

theorem pd_pDen_le_pZ (r s n : ℕ) : pDen 𝕜 W r s n ≤ pZ 𝕜 W r s n := by
  refine sup_le ?_ ?_
  · intro x hx
    refine ⟨pd_F_mono_of_le (by omega) hx.1, ?_⟩
    show W.d n x ∈ W.F (s + r) (n+1)
    exact pd_F_mono_of_le (by omega) hx.2
  · intro x hx
    exact ⟨hx.1, by
      show W.d n x ∈ W.F (s + r) (n+1)
      rw [pd_pB_leib r s n x hx]
      exact Submodule.zero_mem _⟩

theorem pd_pDen_leib (r s n : ℕ) (x : ↥(pZ 𝕜 W r s n))
    (hx : (x : W.C.X n) ∈ pDen 𝕜 W r s n) :
    W.d n (x : W.C.X n) ∈ pDen 𝕜 W r (s + r) (n + 1) := by
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hx
  rw [← hyz, map_add, pd_pB_leib r s n z hz, add_zero]
  refine Submodule.mem_sup.mpr ⟨0, Submodule.zero_mem _, W.d n y, ?_, by simp⟩
  refine ⟨?_, y, ?_, rfl⟩
  · show W.d n y ∈ W.F (s + r) (n + 1)
    exact pd_F_mono_of_le (by omega) hy.2
  · show y ∈ W.F ((s + r) + 1 - r) n
    rw [show (s + r) + 1 - r = s + 1 by omega]
    exact hy.1

theorem pd_pD_apply (r s n : ℕ) (x : ↥(pZ 𝕜 W r s n)) :
    (pD 𝕜 W r s n).hom (Submodule.mkQ ((pDen 𝕜 W r s n).comap (pZ 𝕜 W r s n).subtype) x)
      = Submodule.mkQ ((pDen 𝕜 W r (s + r) (n + 1)).comap (pZ 𝕜 W r (s + r) (n + 1)).subtype)
          (pZmap 𝕜 W r s n x) := by
  have hbranch : (pDen 𝕜 W r s n).comap (pZ 𝕜 W r s n).subtype ≤
      ((pDen 𝕜 W r (s + r) (n + 1)).comap (pZ 𝕜 W r (s + r) (n + 1)).subtype).comap
        (pZmap 𝕜 W r s n) := by
    intro y hy
    have hy' : (y : W.C.X n) ∈ pDen 𝕜 W r s n := hy
    have hres := pd_pDen_leib r s n y hy'
    show ((pZmap 𝕜 W r s n) y : W.C.X (n+1)) ∈ pDen 𝕜 W r (s + r) (n + 1)
    rw [pd_pZmap_apply]
    exact hres
  have hpD : pD 𝕜 W r s n = ModuleCat.ofHom (Submodule.mapQ
      ((pDen 𝕜 W r s n).comap (pZ 𝕜 W r s n).subtype)
      ((pDen 𝕜 W r (s + r) (n + 1)).comap (pZ 𝕜 W r (s + r) (n + 1)).subtype)
      (pZmap 𝕜 W r s n) hbranch) :=
    dif_pos hbranch
  rw [hpD]
  show (Submodule.mapQ ((pDen 𝕜 W r s n).comap (pZ 𝕜 W r s n).subtype)
      ((pDen 𝕜 W r (s + r) (n + 1)).comap (pZ 𝕜 W r (s + r) (n + 1)).subtype)
      (pZmap 𝕜 W r s n) hbranch)
      (Submodule.mkQ ((pDen 𝕜 W r s n).comap (pZ 𝕜 W r s n).subtype) x)
      = Submodule.mkQ ((pDen 𝕜 W r (s + r) (n + 1)).comap (pZ 𝕜 W r (s + r) (n + 1)).subtype)
          (pZmap 𝕜 W r s n x)
  rw [Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.mkQ_apply]


/-! ## 4. Transport of elements along equalities of the degree

The indices of `pZ`, `pB`, `pDen` are `ℕ` and involve truncated subtractions, so
`(n - 1) + 1 = n`, `(s + r) - r + 1 = s + 1` etc. are only propositional, never
definitional.  The following lemmas move elements (and membership) along such equalities.
`W.xcast h` is the linear-map notation for the corresponding transport. -/

theorem pd_xcast_congr {a b : ℕ} (h h' : a = b) (x : W.C.X a) :
    W.xcast h x = W.xcast h' x := by
  rw [Subsingleton.elim h h']

theorem pd_transport_mem' {t t' a b : ℕ} (h : t = t') (h' : a = b) {x : W.C.X a}
    (hx : x ∈ W.F t a) : W.xcast h' x ∈ W.F t' b := by
  cases h
  cases h'
  simpa only [CohFilt.xcast_rfl, LinearMap.id_apply] using hx

theorem pd_xcast_mem_iff {t a b : ℕ} (h : a = b) (x : W.C.X a) :
    W.xcast h x ∈ W.F t b ↔ x ∈ W.F t a := by
  cases h
  simp only [CohFilt.xcast_rfl, LinearMap.id_apply]

theorem pd_xcast_mem_pDen_iff {r s a b : ℕ} (h : a = b) (x : W.C.X a) :
    W.xcast h x ∈ pDen 𝕜 W r s b ↔ x ∈ pDen 𝕜 W r s a := by
  cases h
  simp only [CohFilt.xcast_rfl, LinearMap.id_apply]

theorem pd_xcast_mem_pZ_iff {r s a b : ℕ} (h : a = b) (x : W.C.X a) :
    W.xcast h x ∈ pZ 𝕜 W r s b ↔ x ∈ pZ 𝕜 W r s a := by
  cases h
  simp only [CohFilt.xcast_rfl, LinearMap.id_apply]

theorem pd_xcast_d {a b : ℕ} (h : a = b) (h' : a + 1 = b + 1) (v : W.C.X a) :
    W.xcast h' (W.d a v) = W.d b (W.xcast h v) := by
  cases h
  cases h'
  simp only [CohFilt.xcast_rfl, LinearMap.id_apply]

theorem pd_xcast_mul {a b a' b' : ℕ} (ha : a = b) (hb : a' = b') (u : W.C.X a) (v : W.C.X a') :
    W.xcast (show a + a' = b + b' by omega) (W.mul a a' u v)
      = W.mul b b' (W.xcast ha u) (W.xcast hb v) := by
  cases ha
  cases hb
  simp only [CohFilt.xcast_rfl, LinearMap.id_apply]

theorem pd_dPrev_eq (n : ℕ) (v : W.C.X (n-1)) (hn : 1 ≤ n) :
    W.dPrev n v = W.xcast (show (n-1)+1 = n by omega) (W.d (n-1) v) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simp only [CohFilt.dPrev, CohFilt.d, CohFilt.xcast, CategoryTheory.eqToHom_refl,
    ModuleCat.hom_id, LinearMap.id_apply]
  rfl

theorem pd_mem_pB_succ {r s n : ℕ} {z : W.C.X (n+1)} :
    z ∈ pB 𝕜 W r s (n+1) ↔ z ∈ W.F s (n+1) ∧ ∃ w : W.C.X n, w ∈ W.F (s+1-r) n ∧ W.d n w = z := by
  rw [pB, Submodule.mem_inf, Submodule.mem_map]
  constructor
  · rintro ⟨h1, w, hw, hwz⟩; exact ⟨h1, w, hw, hwz⟩
  · rintro ⟨h1, w, hw, hwz⟩; exact ⟨h1, w, hw, hwz⟩

/-! ## 5. The product on the cycles and its descent to the pages -/

theorem pd_pZ_mul (r s n s' n' : ℕ) (x : ↥(pZ 𝕜 W r s n)) (y : ↥(pZ 𝕜 W r s' n')) :
    W.mul n n' (x : W.C.X n) (y : W.C.X n') ∈ pZ 𝕜 W r (s + s') (n + n') := by
  refine ⟨W.mul_filt s s' n n' _ _ x.2.1 y.2.1, ?_⟩
  have e1 : (n+1) + n' = n + n' + 1 := by omega
  have e2 : n + (n'+1) = n + n' + 1 := by omega
  have hL := W.mul_leib n n' e1 e2 (x : W.C.X n) (y : W.C.X n')
  show (W.C.d (n + n') (n + n' + 1)).hom (W.mul n n' (x : W.C.X n) (y : W.C.X n'))
      ∈ W.F ((s + s') + r) (n + n' + 1)
  rw [hL]
  refine Submodule.add_mem _ ?_ ?_
  · exact pd_transport_mem' (h := show (s+r)+s' = (s+s')+r by omega) (h' := e1)
      (W.mul_filt (s+r) s' (n+1) n' _ _ x.2.2 y.2.1)
  · exact Submodule.smul_mem _ (((-1 : 𝕜)^n))
      (pd_transport_mem' (h := show s+(s'+r) = (s+s')+r by omega) (h' := e2)
        (W.mul_filt s (s'+r) n (n'+1) _ _ x.2.1 y.2.2))


/-- The product of a denominator element with a cycle stays in the denominator. -/
theorem pd_pDen_mul_left (r s n s' n' : ℕ) (x : ↥(pZ 𝕜 W r s n)) (y : ↥(pZ 𝕜 W r s' n'))
    (hx : (x : W.C.X n) ∈ pDen 𝕜 W r s n) :
    W.mul n n' (x : W.C.X n) (y : W.C.X n') ∈ pDen 𝕜 W r (s + s') (n + n') := by
  obtain ⟨xu, hxu, xb, hxb, hxub⟩ := Submodule.mem_sup.mp hx
  have hsplit : W.mul n n' (x : W.C.X n) (y : W.C.X n')
      = W.mul n n' xu (y : W.C.X n') + W.mul n n' xb (y : W.C.X n') := by
    rw [← hxub, map_add, LinearMap.add_apply]
  rw [hsplit]
  refine Submodule.add_mem _ ?_ ?_
  · -- first summand: `xu ∈ Z_{r-1}^{s+1}`
    refine Submodule.mem_sup.mpr ⟨W.mul n n' xu (y : W.C.X n'), ⟨?_, ?_⟩, 0, Submodule.zero_mem _,
      by simp⟩
    · have h1 := W.mul_filt (s+1) s' n n' xu (y : W.C.X n') hxu.1 y.2.1
      rwa [show (s+1)+s' = s+s'+1 by omega] at h1
    · have e1 : (n+1)+n' = n+n'+1 := by omega
      have e2 : n+(n'+1) = n+n'+1 := by omega
      have hL := W.mul_leib n n' e1 e2 xu (y : W.C.X n')
      show (W.C.d (n+n') (n+n'+1)).hom (W.mul n n' xu (y : W.C.X n'))
          ∈ W.F ((s+s'+1)+(r-1)) (n+n'+1)
      rw [hL]
      refine Submodule.add_mem _ ?_ ?_
      · exact pd_transport_mem' (h := show (s+1)+(r-1)+s' = (s+s'+1)+(r-1) by omega) (h' := e1)
          (W.mul_filt ((s+1)+(r-1)) s' (n+1) n' _ _ hxu.2 y.2.1)
      · refine Submodule.smul_mem _ (((-1 : 𝕜)^n)) ?_
        refine pd_transport_mem (h := e2) ?_
        exact pd_F_mono_of_le (show (s+s'+1)+(r-1) ≤ (s+1)+(s'+r) by omega)
          (W.mul_filt (s+1) (s'+r) n (n'+1) _ _ hxu.1 y.2.2)
  · -- second summand: `xb ∈ B_r^s`
    cases n with
    | zero =>
      rw [pd_pB_zero, Submodule.mem_bot] at hxb
      rw [hxb]
      simp
    | succ k =>
      obtain ⟨_hxF, w, hw, hwx⟩ := (pd_mem_pB_succ (r := r) (s := s) (n := k) (z := xb)).mp hxb
      have eτ : (k+1)+n' = k+n'+1 := by omega
      have e₂ : k+(n'+1) = k+n'+1 := by omega
      have hLeib : (W.C.d (k+n') (k+n'+1)).hom (W.mul k n' (w : W.C.X k) (y : W.C.X n'))
          = W.xcast eτ (W.mul (k+1) n' ((W.d k) (w : W.C.X k)) (y : W.C.X n'))
            + (-1 : 𝕜)^k • W.xcast e₂
                (W.mul k (n'+1) (w : W.C.X k) ((W.d n') (y : W.C.X n'))) := by
        have h := W.mul_leib k n' eτ e₂ (w : W.C.X k) (y : W.C.X n')
        simpa only [CohFilt.xcast, CohFilt.d] using h
      have hu : W.xcast eτ (W.mul (k+1) n' xb (y : W.C.X n'))
          = (W.C.d (k+n') (k+n'+1)).hom (W.mul k n' (w : W.C.X k) (y : W.C.X n'))
            - (-1 : 𝕜)^k • W.xcast e₂
                (W.mul k (n'+1) (w : W.C.X k) ((W.d n') (y : W.C.X n'))) := by
        rw [← hwx, hLeib, add_sub_cancel_right]
      refine (pd_xcast_mem_pDen_iff (h := eτ)
        (x := W.mul (k+1) n' xb (y : W.C.X n'))).mp ?_
      rw [hu]
      refine Submodule.sub_mem _ ?_ ?_
      · -- the `d(u)` term lies in `B_r^{s+s'}`
        refine Submodule.mem_sup.mpr ⟨0, Submodule.zero_mem _,
          (W.C.d (k+n') (k+n'+1)).hom (W.mul k n' (w : W.C.X k) (y : W.C.X n')), ?_, by simp⟩
        refine (pd_mem_pB_succ (r := r) (s := s+s') (n := k+n')
          (z := (W.C.d (k+n') (k+n'+1)).hom (W.mul k n' (w : W.C.X k) (y : W.C.X n')))).mpr
          ⟨?_, W.mul k n' (w : W.C.X k) (y : W.C.X n'), ?_, rfl⟩
        · -- `d(u) ∈ F^{s+s'}`
          rw [hLeib]
          refine Submodule.add_mem _ ?_ ?_
          · rw [hwx]
            exact pd_transport_mem (h := eτ) (W.mul_filt s s' (k+1) n' _ _ hxb.1 y.2.1)
          · refine Submodule.smul_mem _ _ ?_
            refine pd_transport_mem (h := e₂)
              (pd_F_mono_of_le (show s+s' ≤ (s+1-r)+(s'+r) by omega)
                (W.mul_filt (s+1-r) (s'+r) k (n'+1) _ _ hw y.2.2))
        · -- `u ∈ F^{(s+s')-r+1}`
          have harith : (s+s')+1-r ≤ (s+1-r)+s' := by
            by_cases h : r ≤ s+1
            · have h2 := Nat.add_sub_assoc h s'
              omega
            · omega
          exact pd_F_mono_of_le harith
            (W.mul_filt (s+1-r) s' k n' _ _ hw y.2.1)
      · -- the `v` term lies in `Z_{r-1}^{s+s'+1}`
        refine Submodule.smul_mem _ _ ?_
        refine Submodule.mem_sup.mpr ⟨W.xcast e₂ (W.mul k (n'+1) (w : W.C.X k) ((W.d n') (y : W.C.X n'))),
          ⟨?_, ?_⟩, 0, Submodule.zero_mem _, by simp⟩
        · -- `xcast e₂ v ∈ F^{s+s'+1}`
          exact pd_transport_mem (h := e₂)
            (pd_F_mono_of_le (show s+s'+1 ≤ (s+1-r)+(s'+r) by omega)
              (W.mul_filt (s+1-r) (s'+r) k (n'+1) _ _ hw y.2.2))
        · -- `d (xcast e₂ v) ∈ F^{(s+s'+1)+(r-1)}`
          show W.d (k+n'+1) (W.xcast e₂ (W.mul k (n'+1) (w : W.C.X k) ((W.d n') (y : W.C.X n'))))
              ∈ W.F ((s+s'+1)+(r-1)) ((k+n'+1)+1)
          rw [← pd_xcast_d e₂ (show (k+(n'+1))+1 = (k+n'+1)+1 by omega)]
          refine pd_transport_mem (h := show (k+(n'+1))+1 = (k+n'+1)+1 by omega) ?_
          have e₃ : (k+1)+(n'+1) = k+(n'+1)+1 := by omega
          have e₄ : k+((n'+1)+1) = k+(n'+1)+1 := by omega
          have hLeib2 : (W.C.d (k+(n'+1)) (k+(n'+1)+1)).hom
                (W.mul k (n'+1) (w : W.C.X k) ((W.d n') (y : W.C.X n')))
              = W.xcast e₃ (W.mul (k+1) (n'+1) ((W.d k) (w : W.C.X k))
                  ((W.d n') (y : W.C.X n')))
                + (-1 : 𝕜)^k • W.xcast e₄ (W.mul k ((n'+1)+1) (w : W.C.X k)
                    ((W.d (n'+1)) ((W.d n') (y : W.C.X n')))) := by
            have h := W.mul_leib k (n'+1) e₃ e₄ (w : W.C.X k) ((W.d n') (y : W.C.X n'))
            simpa only [CohFilt.xcast, CohFilt.d] using h
          have hzero : W.mul k ((n'+1)+1) (w : W.C.X k)
              (W.d (n'+1) (W.d n' (y : W.C.X n'))) = 0 := by
            rw [pd_d_comp_d_apply, map_zero]
          show (W.C.d (k+(n'+1)) (k+(n'+1)+1)).hom
              (W.mul k (n'+1) (w : W.C.X k) ((W.d n') (y : W.C.X n')))
              ∈ W.F ((s+s'+1)+(r-1)) ((k+(n'+1))+1)
          rw [hLeib2, hzero, map_zero, smul_zero, add_zero]
          refine pd_transport_mem (h := e₃) ?_
          have hbnd : xb ∈ W.F (max s (s + 1 - r)) (k+1) := by
            rcases le_total s (s + 1 - r) with h | h
            · rw [max_eq_right h]; rw [← hwx]; exact W.F_leib (s+1-r) k w hw
            · rw [max_eq_left h]; exact hxb.1
          refine pd_F_mono_of_le (show (s+s'+1)+(r-1) ≤ max s (s + 1 - r) + (s'+r) by
            rcases le_total s (s + 1 - r) with h | h
            · rw [max_eq_right h]; omega
            · rw [max_eq_left h]; omega) ?_
          rw [hwx]
          exact W.mul_filt (max s (s + 1 - r)) (s'+r) (k+1) (n'+1) _ _ hbnd y.2.2



/-- The product of a cycle with a denominator element stays in the denominator. -/
theorem pd_pDen_mul_right (r s n s' n' : ℕ) (x : ↥(pZ 𝕜 W r s n)) (y : ↥(pZ 𝕜 W r s' n'))
    (hy : (y : W.C.X n') ∈ pDen 𝕜 W r s' n') :
    W.mul n n' (x : W.C.X n) (y : W.C.X n') ∈ pDen 𝕜 W r (s + s') (n + n') := by
  obtain ⟨yu, hyu, yb, hyb, hyub⟩ := Submodule.mem_sup.mp hy
  have hsplit : W.mul n n' (x : W.C.X n) (y : W.C.X n')
      = W.mul n n' (x : W.C.X n) yu + W.mul n n' (x : W.C.X n) yb := by
    rw [← hyub, map_add]
  rw [hsplit]
  refine Submodule.add_mem _ ?_ ?_
  · -- first summand: `yu ∈ Z_{r-1}^{s'+1}`
    refine Submodule.mem_sup.mpr ⟨W.mul n n' (x : W.C.X n) yu, ⟨?_, ?_⟩, 0, Submodule.zero_mem _,
      by simp⟩
    · have h1 := W.mul_filt s (s'+1) n n' (x : W.C.X n) yu x.2.1 hyu.1
      rwa [show s+(s'+1) = s+s'+1 by omega] at h1
    · have e1 : (n+1)+n' = n+n'+1 := by omega
      have e2 : n+(n'+1) = n+n'+1 := by omega
      have hL := W.mul_leib n n' e1 e2 (x : W.C.X n) yu
      show (W.C.d (n+n') (n+n'+1)).hom (W.mul n n' (x : W.C.X n) yu)
          ∈ W.F ((s+s'+1)+(r-1)) (n+n'+1)
      rw [hL]
      refine Submodule.add_mem _ ?_ ?_
      · refine pd_transport_mem (h := e1)
          (pd_F_mono_of_le (show (s+s'+1)+(r-1) ≤ (s+r)+(s'+1) by omega)
            (W.mul_filt (s+r) (s'+1) (n+1) n' _ _ x.2.2 hyu.1))
      · refine Submodule.smul_mem _ _ ?_
        refine pd_transport_mem (h := e2)
          (pd_F_mono_of_le (show (s+s'+1)+(r-1) ≤ s+((s'+1)+(r-1)) by omega)
            (W.mul_filt s ((s'+1)+(r-1)) n (n'+1) _ _ x.2.1 hyu.2))
  · -- second summand: `yb ∈ B_r^{s'}`
    cases n' with
    | zero =>
      rw [pd_pB_zero, Submodule.mem_bot] at hyb
      rw [hyb]
      simp
    | succ k =>
      obtain ⟨_hyF, w, hw, hwy⟩ := (pd_mem_pB_succ (r := r) (s := s') (n := k) (z := yb)).mp hyb
      have e₂ : n+(k+1) = n+k+1 := by omega
      have e₁ : (n+1)+k = n+k+1 := by omega
      have hLeib : (W.C.d (n+k) (n+k+1)).hom (W.mul n k (x : W.C.X n) (w : W.C.X k))
          = W.xcast e₁ (W.mul (n+1) k ((W.d n) (x : W.C.X n)) (w : W.C.X k))
            + (-1 : 𝕜)^n • W.xcast e₂
                (W.mul n (k+1) (x : W.C.X n) ((W.d k) (w : W.C.X k))) := by
        have h := W.mul_leib n k e₁ e₂ (x : W.C.X n) (w : W.C.X k)
        simpa only [CohFilt.xcast, CohFilt.d] using h
      have hX : W.xcast e₂ (W.mul n (k+1) (x : W.C.X n) yb)
          = (-1 : 𝕜)^n • ((W.C.d (n+k) (n+k+1)).hom (W.mul n k (x : W.C.X n) (w : W.C.X k))
              - W.xcast e₁ (W.mul (n+1) k ((W.d n) (x : W.C.X n)) (w : W.C.X k))) := by
        rw [← hwy, hLeib, add_sub_cancel_left, smul_smul]
        rw [show ((-1 : 𝕜)^n) * ((-1 : 𝕜)^n) = 1 by rw [← mul_pow]; simp, one_smul]
      refine (pd_xcast_mem_pDen_iff (h := e₂)
        (x := W.mul n (k+1) (x : W.C.X n) yb)).mp ?_
      rw [hX]
      refine Submodule.smul_mem _ _ ?_
      refine Submodule.sub_mem _ ?_ ?_
      · -- the `d(u)` term lies in `B_r^{s+s'}`
        refine Submodule.mem_sup.mpr ⟨0, Submodule.zero_mem _,
          (W.C.d (n+k) (n+k+1)).hom (W.mul n k (x : W.C.X n) (w : W.C.X k)), ?_, by simp⟩
        refine (pd_mem_pB_succ (r := r) (s := s+s') (n := n+k)
          (z := (W.C.d (n+k) (n+k+1)).hom (W.mul n k (x : W.C.X n) (w : W.C.X k)))).mpr
          ⟨?_, W.mul n k (x : W.C.X n) (w : W.C.X k), ?_, rfl⟩
        · -- `d(u) ∈ F^{s+s'}`
          rw [hLeib]
          refine Submodule.add_mem _ ?_ ?_
          · refine pd_transport_mem (h := e₁)
              (pd_F_mono_of_le (show s+s' ≤ (s+r)+(s'+1-r) by omega)
                (W.mul_filt (s+r) (s'+1-r) (n+1) k _ _ x.2.2 hw))
          · refine Submodule.smul_mem _ _ ?_
            refine pd_transport_mem (h := e₂) ?_
            rw [hwy]
            exact W.mul_filt s s' n (k+1) _ _ x.2.1 hyb.1
        · -- `u ∈ F^{(s+s')-r+1}`
          have harith : (s+s')+1-r ≤ s+(s'+1-r) := by
            by_cases h : r ≤ s'+1
            · have h2 := Nat.add_sub_assoc h s
              omega
            · omega
          exact pd_F_mono_of_le harith
            (W.mul_filt s (s'+1-r) n k _ _ x.2.1 hw)
      · -- the `d (dy)` term lies in `Z_{r-1}^{s+s'+1}`
        refine Submodule.mem_sup.mpr
          ⟨W.xcast e₁ (W.mul (n+1) k ((W.d n) (x : W.C.X n)) (w : W.C.X k)),
            ⟨?_, ?_⟩, 0, Submodule.zero_mem _, by simp⟩
        · -- `∈ F^{s+s'+1}`
          refine pd_transport_mem (h := e₁)
            (pd_F_mono_of_le (show s+s'+1 ≤ (s+r)+(s'+1-r) by omega)
              (W.mul_filt (s+r) (s'+1-r) (n+1) k _ _ x.2.2 hw))
        · -- `d (...) ∈ F^{(s+s'+1)+(r-1)}`
          show W.d (n+k+1) (W.xcast e₁ (W.mul (n+1) k ((W.d n) (x : W.C.X n)) (w : W.C.X k)))
              ∈ W.F ((s+s'+1)+(r-1)) ((n+k+1)+1)
          rw [← pd_xcast_d e₁ (show ((n+1)+k)+1 = (n+k+1)+1 by omega)]
          refine pd_transport_mem (h := show ((n+1)+k)+1 = (n+k+1)+1 by omega) ?_
          have e₃ : (n+2)+k = (n+1)+k+1 := by omega
          have e₄ : (n+1)+(k+1) = (n+1)+k+1 := by omega
          have hLeib2 : (W.C.d ((n+1)+k) ((n+1)+k+1)).hom
                (W.mul (n+1) k ((W.d n) (x : W.C.X n)) (w : W.C.X k))
              = W.xcast e₃ (W.mul (n+2) k ((W.d (n+1)) ((W.d n) (x : W.C.X n))) (w : W.C.X k))
                + (-1 : 𝕜)^(n+1) • W.xcast e₄ (W.mul (n+1) (k+1)
                    ((W.d n) (x : W.C.X n)) ((W.d k) (w : W.C.X k))) := by
            have h := W.mul_leib (n+1) k e₃ e₄ ((W.d n) (x : W.C.X n)) (w : W.C.X k)
            simpa only [CohFilt.xcast, CohFilt.d] using h
          have hzero : W.mul (n+2) k (W.d (n+1) (W.d n (x : W.C.X n))) (w : W.C.X k) = 0 := by
            rw [pd_d_comp_d_apply, map_zero, LinearMap.zero_apply]
          show (W.C.d ((n+1)+k) ((n+1)+k+1)).hom
              (W.mul (n+1) k ((W.d n) (x : W.C.X n)) (w : W.C.X k))
              ∈ W.F ((s+s'+1)+(r-1)) (((n+1)+k)+1)
          rw [hLeib2, hzero, map_zero, zero_add]
          refine Submodule.smul_mem _ _ ?_
          refine pd_transport_mem (h := e₄) ?_
          have hbnd : yb ∈ W.F (max s' (s' + 1 - r)) (k+1) := by
            rcases le_total s' (s' + 1 - r) with h | h
            · rw [max_eq_right h]; rw [← hwy]; exact W.F_leib (s'+1-r) k w hw
            · rw [max_eq_left h]; exact hyb.1
          refine pd_F_mono_of_le (show (s+s'+1)+(r-1) ≤ (s+r) + max s' (s' + 1 - r) by
            rcases le_total s' (s' + 1 - r) with h | h
            · rw [max_eq_right h]; omega
            · rw [max_eq_left h]; omega) ?_
          rw [hwy]
          exact W.mul_filt (s+r) (max s' (s'+1-r)) (n+1) (k+1) _ _ x.2.2 hbnd


/-! ## 6. The product on the cycles and on the pages -/

/-- The product of two cycles, as a bilinear map. -/
noncomputable def pd_mulZ (r s n s' n' : ℕ) :
    (↥(pZ 𝕜 W r s n)) →ₗ[𝕜] (↥(pZ 𝕜 W r s' n')) →ₗ[𝕜]
      (↥(pZ 𝕜 W r (s+s') (n+n'))) :=
  { toFun := fun x =>
      LinearMap.codRestrict (pZ 𝕜 W r (s+s') (n+n'))
        ((((W.mul n n').comp (Submodule.subtype (pZ 𝕜 W r s n))) x).comp
          (Submodule.subtype (pZ 𝕜 W r s' n')))
        (fun y => pd_pZ_mul r s n s' n' x y)
    map_add' := fun x1 x2 => by
      ext y
      show W.mul n n' ((x1 : W.C.X n) + (x2 : W.C.X n)) (y : W.C.X n')
        = W.mul n n' (x1 : W.C.X n) (y : W.C.X n') + W.mul n n' (x2 : W.C.X n) (y : W.C.X n')
      rw [map_add, LinearMap.add_apply]
    map_smul' := fun c x => by
      ext y
      show W.mul n n' (c • (x : W.C.X n)) (y : W.C.X n')
        = c • W.mul n n' (x : W.C.X n) (y : W.C.X n')
      rw [map_smul, LinearMap.smul_apply] }

theorem pd_mulZ_val (r s n s' n' : ℕ) (x : ↥(pZ 𝕜 W r s n)) (y : ↥(pZ 𝕜 W r s' n')) :
    ((pd_mulZ r s n s' n' x y : ↥(pZ 𝕜 W r (s+s') (n+n'))) : W.C.X (n+n')) =
      W.mul n n' (x : W.C.X n) (y : W.C.X n') := rfl

/-- The product of cycles, followed by the projection onto the page. -/
noncomputable def pd_mulZQ (r s n s' n' : ℕ) :
    (↥(pZ 𝕜 W r s n)) →ₗ[𝕜] (↥(pZ 𝕜 W r s' n')) →ₗ[𝕜]
      (pEraw 𝕜 W r (s+s') (n+n')) :=
  LinearMap.mk₂ (R := 𝕜) (M := (↥(pZ 𝕜 W r s n))) (Nₗ := (↥(pZ 𝕜 W r s' n')))
    (Pₗ := (pEraw 𝕜 W r (s+s') (n+n')))
    (fun x y => Submodule.mkQ ((pDen 𝕜 W r (s+s') (n+n')).comap
      (pZ 𝕜 W r (s+s') (n+n')).subtype) (pd_mulZ r s n s' n' x y))
    (fun x1 x2 y => by
      rw [map_add (pd_mulZ r s n s' n'), LinearMap.add_apply, map_add (Submodule.mkQ _)]
      rfl)
    (fun c x y => by
      rw [map_smul (pd_mulZ r s n s' n'), LinearMap.smul_apply, map_smul (Submodule.mkQ _)]
      rfl)
    (fun x y1 y2 => by
      rw [map_add (pd_mulZ r s n s' n' x), map_add (Submodule.mkQ _)]
      rfl)
    (fun c x y => by
      rw [map_smul (pd_mulZ r s n s' n' x), map_smul (Submodule.mkQ _)]
      rfl)

theorem pd_mulZQ_val (r s n s' n' : ℕ) (x : ↥(pZ 𝕜 W r s n)) (y : ↥(pZ 𝕜 W r s' n')) :
    pd_mulZQ r s n s' n' x y
      = Submodule.mkQ ((pDen 𝕜 W r (s+s') (n+n')).comap (pZ 𝕜 W r (s+s') (n+n')).subtype)
          (pd_mulZ r s n s' n' x y) := rfl

/-- The left descent condition for the product. -/
theorem pd_mulKer_left (r s n s' n' : ℕ) :
    ((pDen 𝕜 W r s n).comap (pZ 𝕜 W r s n).subtype) ≤ (pd_mulZQ r s n s' n').ker := by
  intro x hx
  rw [LinearMap.mem_ker]
  ext y
  show Submodule.mkQ ((pDen 𝕜 W r (s+s') (n+n')).comap
      (pZ 𝕜 W r (s+s') (n+n')).subtype) (pd_mulZ r s n s' n' x y) = 0
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  simpa only [pd_mulZ_val, Submodule.mem_comap, Submodule.coe_subtype] using pd_pDen_mul_left r s n s' n' x y hx

/-- The right descent condition for the product. -/
theorem pd_mulKer_right (r s n s' n' : ℕ) :
    ((pDen 𝕜 W r s' n').comap (pZ 𝕜 W r s' n').subtype) ≤ (pd_mulZQ r s n s' n').flip.ker := by
  intro y hy
  rw [LinearMap.mem_ker]
  ext x
  rw [LinearMap.flip_apply]
  show Submodule.mkQ ((pDen 𝕜 W r (s+s') (n+n')).comap
      (pZ 𝕜 W r (s+s') (n+n')).subtype) (pd_mulZ r s n s' n' x y) = 0
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  simpa only [pd_mulZ_val, Submodule.mem_comap, Submodule.coe_subtype] using pd_pDen_mul_right r s n s' n' x y hy

/-- The product on the pages `E_r`, induced by the product on the cycles. -/
noncomputable def pd_mul (r s n s' n' : ℕ) :
    (pEraw 𝕜 W r s n) →ₗ[𝕜] (pEraw 𝕜 W r s' n') →ₗ[𝕜] (pEraw 𝕜 W r (s+s') (n+n')) :=
  LinearMap.liftQ₂ ((pDen 𝕜 W r s n).comap (pZ 𝕜 W r s n).subtype)
    ((pDen 𝕜 W r s' n').comap (pZ 𝕜 W r s' n').subtype) (pd_mulZQ r s n s' n')
    (pd_mulKer_left r s n s' n') (pd_mulKer_right r s n s' n')

theorem pd_mul_eq (r s n s' n' : ℕ) :
    pd_mul r s n s' n' = LinearMap.liftQ₂ ((pDen 𝕜 W r s n).comap (pZ 𝕜 W r s n).subtype)
      ((pDen 𝕜 W r s' n').comap (pZ 𝕜 W r s' n').subtype) (pd_mulZQ r s n s' n')
      (pd_mulKer_left r s n s' n') (pd_mulKer_right r s n s' n') := rfl

theorem pd_mul_nat (r s n s' n' : ℕ) (x : ↥(pZ 𝕜 W r s n)) (y : ↥(pZ 𝕜 W r s' n')) :
    (pd_mul r s n s' n')
        (Submodule.mkQ ((pDen 𝕜 W r s n).comap (pZ 𝕜 W r s n).subtype) x)
        (Submodule.mkQ ((pDen 𝕜 W r s' n').comap (pZ 𝕜 W r s' n').subtype) y)
      = Submodule.mkQ ((pDen 𝕜 W r (s+s') (n+n')).comap (pZ 𝕜 W r (s+s') (n+n')).subtype)
          (pd_mulZ r s n s' n' x y) := by
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, pd_mul_eq]
  rw [← pd_mulZQ_val r s n s' n' x y]
  exact LinearMap.liftQ₂_mk (pd_mulKer_left r s n s' n') (pd_mulKer_right r s n s' n') x y

/-! ## 7. The projection `ker d_r → E_{r+1}` -/

/-- The cycles whose coboundary lies in the denominator `D_r` — the preimage of `ker d_r` in `Z_r^s`. -/
def pd_K (𝕜 : Type) [Field 𝕜] (W : CohFilt 𝕜) (r s n : ℕ) : Submodule 𝕜 (W.C.X n) :=
  pZ 𝕜 W r s n ⊓ (pDen 𝕜 W r (s+r) (n+1)).comap (W.d n)

theorem pd_pDen_le_K (r s n : ℕ) : pDen 𝕜 W r s n ≤ pd_K 𝕜 W r s n := by
  refine le_inf (pd_pDen_le_pZ r s n) ?_
  intro x hx
  exact pd_pDen_leib r s n ⟨x, pd_pDen_le_pZ r s n hx⟩ hx

theorem pd_pZ_succ_le_K (r s n : ℕ) : pZ 𝕜 W (r+1) s n ≤ pd_K 𝕜 W r s n := by
  refine le_inf (pd_pZ_anti (Nat.le_succ r) le_rfl) ?_
  intro x hx
  have hxZ : W.d n x ∈ pZ 𝕜 W (r-1) (s+r+1) (n+1) := by
    refine ⟨hx.2, ?_⟩
    show W.d (n+1) (W.d n x) ∈ W.F ((s+r+1)+(r-1)) (n+1+1)
    rw [pd_d_comp_d_apply]
    exact Submodule.zero_mem _
  exact Submodule.mem_sup.mpr ⟨_, hxZ, 0, Submodule.zero_mem _, by simp⟩

theorem pd_pZ_succ_inter_pDen_le (r s n : ℕ) :
    pZ 𝕜 W (r+1) s n ⊓ pDen 𝕜 W r s n ≤ pDen 𝕜 W (r+1) s n := by
  intro x hx
  obtain ⟨hxZ, hxD⟩ := hx
  obtain ⟨z₁, hz₁, b, hb, hzb⟩ := Submodule.mem_sup.mp hxD
  have hdz : W.d n z₁ = W.d n x := by
    rw [show W.d n x = W.d n z₁ + W.d n b from by rw [← hzb, map_add],
      pd_pB_leib r s n b hb, add_zero]
  have hz₁Z : z₁ ∈ pZ 𝕜 W r (s+1) n := by
    refine ⟨hz₁.1, ?_⟩
    show W.d n z₁ ∈ W.F (s+1+r) (n+1)
    rw [show s+1+r = s+r+1 by omega, hdz]
    exact hxZ.2
  have hbB : b ∈ pB 𝕜 W (r+1) s n := pd_pB_mono (Nat.le_succ r) hb
  exact Submodule.mem_sup.mpr ⟨z₁, hz₁Z, b, hbB, hzb⟩

theorem pd_exists_lift (𝕜 : Type) [Field 𝕜] (W : CohFilt 𝕜) (r s n : ℕ) (x : ↥(pd_K 𝕜 W r s n)) :
    ∃ z : ↥(pZ 𝕜 W (r+1) s n), x.1 - z.1 ∈ pDen 𝕜 W r s n := by
  obtain ⟨hxZ, hxK⟩ := x.2
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hxK
  obtain ⟨_hvF, w, hw, hwv⟩ := (pd_mem_pB_succ (r := r) (s := s+r) (n := n) (z := v)).mp hv
  have hw' : w ∈ W.F (s+1) n := by
    rw [show (s+r)+1-r = s+1 from by omega] at hw
    exact hw
  refine ⟨⟨x.1 - w, ?_, ?_⟩, ?_⟩
  · show x.1 - w ∈ W.F s n
    exact Submodule.sub_mem _ hxZ.1 (pd_F_mono_of_le (by omega) hw')
  · show W.d n (x.1 - w) ∈ W.F (s+(r+1)) (n+1)
    rw [map_sub, show W.d n x.1 = u + v from huv.symm, hwv, add_sub_cancel_right]
    exact hu.1
  · show x.1 - (x.1 - w) ∈ pDen 𝕜 W r s n
    rw [sub_sub_cancel]
    have hv' : v ∈ W.F (max (s+r) (s+1)) (n+1) := by
      rcases le_total (s+1) (s+r) with h | h
      · rw [max_eq_left h]; exact hv.1
      · rw [max_eq_right h, ← hwv]; exact W.F_leib (s+1) n w hw'
    refine Submodule.mem_sup.mpr ⟨w, ⟨hw', ?_⟩, 0, Submodule.zero_mem _, by simp⟩
    show W.d n w ∈ W.F ((s+1)+(r-1)) (n+1)
    have hineq : (s+1)+(r-1) ≤ max (s+r) (s+1) := by
      rcases le_total (s+1) (s+r) with h | h
      · rw [max_eq_left h]; omega
      · rw [max_eq_right h]; omega
    rw [hwv]
    exact pd_F_mono_of_le hineq hv'

noncomputable def pd_lift (𝕜 : Type) [Field 𝕜] (W : CohFilt 𝕜) (r s n : ℕ) (x : ↥(pd_K 𝕜 W r s n)) : ↥(pZ 𝕜 W (r+1) s n) :=
  Classical.choose (pd_exists_lift 𝕜 W r s n x)

theorem pd_lift_spec (𝕜 : Type) [Field 𝕜] (W : CohFilt 𝕜) (r s n : ℕ) (x : ↥(pd_K 𝕜 W r s n)) :
    x.1 - (pd_lift 𝕜 W r s n x).1 ∈ pDen 𝕜 W r s n :=
  Classical.choose_spec (pd_exists_lift 𝕜 W r s n x)

theorem pd_lift_eq_of (𝕜 : Type) [Field 𝕜] (W : CohFilt 𝕜) (r s n : ℕ) (x : ↥(pd_K 𝕜 W r s n)) (z : ↥(pZ 𝕜 W (r+1) s n))
    (hz : x.1 - z.1 ∈ pDen 𝕜 W r s n) :
    Submodule.mkQ ((pDen 𝕜 W (r+1) s n).comap (pZ 𝕜 W (r+1) s n).subtype)
        (pd_lift 𝕜 W r s n x)
      = Submodule.mkQ ((pDen 𝕜 W (r+1) s n).comap (pZ 𝕜 W (r+1) s n).subtype) z := by
  have hzp : ((pd_lift 𝕜 W r s n x : ↥(pZ 𝕜 W (r+1) s n)) - z : W.C.X n) ∈ pDen 𝕜 W r s n := by
    show ((pd_lift 𝕜 W r s n x).1 - z.1) ∈ pDen 𝕜 W r s n
    rw [show (pd_lift 𝕜 W r s n x).1 - z.1
        = (x.1 - z.1) - (x.1 - (pd_lift 𝕜 W r s n x).1)
        from by abel]
    exact Submodule.sub_mem _ hz (pd_lift_spec 𝕜 W r s n x)
  have hmem : ((pd_lift 𝕜 W r s n x : ↥(pZ 𝕜 W (r+1) s n)) - z : W.C.X n)
      ∈ pZ 𝕜 W (r+1) s n ⊓ pDen 𝕜 W r s n :=
    ⟨(pZ 𝕜 W (r+1) s n).sub_mem (pd_lift 𝕜 W r s n x).2 z.2, hzp⟩
  have hD : ((pd_lift 𝕜 W r s n x : ↥(pZ 𝕜 W (r+1) s n)) - z : W.C.X n)
      ∈ pDen 𝕜 W (r+1) s n := pd_pZ_succ_inter_pDen_le r s n hmem
  rw [← sub_eq_zero]
  rw [← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact hD

noncomputable def pd_pFun (𝕜 : Type) [Field 𝕜] (W : CohFilt 𝕜) (r s n : ℕ) :
    ↥(pd_K 𝕜 W r s n) →ₗ[𝕜] pEraw 𝕜 W (r+1) s n :=
  { toFun := fun x => Submodule.mkQ
      ((pDen 𝕜 W (r+1) s n).comap (pZ 𝕜 W (r+1) s n).subtype) (pd_lift 𝕜 W r s n x)
    map_add' := fun x1 x2 => by
      show Submodule.mkQ ((pDen 𝕜 W (r+1) s n).comap (pZ 𝕜 W (r+1) s n).subtype)
            (pd_lift 𝕜 W r s n (x1 + x2))
          = Submodule.mkQ ((pDen 𝕜 W (r+1) s n).comap (pZ 𝕜 W (r+1) s n).subtype)
              (pd_lift 𝕜 W r s n x1)
            + Submodule.mkQ ((pDen 𝕜 W (r+1) s n).comap (pZ 𝕜 W (r+1) s n).subtype)
              (pd_lift 𝕜 W r s n x2)
      rw [pd_lift_eq_of 𝕜 W r s n (x1 + x2)
        (pd_lift 𝕜 W r s n x1 + pd_lift 𝕜 W r s n x2) (by
          show (x1.1 + x2.1) - ((pd_lift 𝕜 W r s n x1).1 + (pd_lift 𝕜 W r s n x2).1)
            ∈ pDen 𝕜 W r s n
          rw [show x1.1 + x2.1 - ((pd_lift 𝕜 W r s n x1).1 + (pd_lift 𝕜 W r s n x2).1)
              = (x1.1 - (pd_lift 𝕜 W r s n x1).1) + (x2.1 - (pd_lift 𝕜 W r s n x2).1)
              from by abel]
          exact Submodule.add_mem _ (pd_lift_spec 𝕜 W r s n x1) (pd_lift_spec 𝕜 W r s n x2)),
        map_add]
    map_smul' := fun c x => by
      show Submodule.mkQ ((pDen 𝕜 W (r+1) s n).comap (pZ 𝕜 W (r+1) s n).subtype)
            (pd_lift 𝕜 W r s n (c • x))
          = c • Submodule.mkQ ((pDen 𝕜 W (r+1) s n).comap (pZ 𝕜 W (r+1) s n).subtype)
              (pd_lift 𝕜 W r s n x)
      rw [pd_lift_eq_of 𝕜 W r s n (c • x) (c • pd_lift 𝕜 W r s n x) (by
        rw [show (c • x).1 = c • x.1 from rfl,
          show (c • pd_lift 𝕜 W r s n x).1 = c • (pd_lift 𝕜 W r s n x).1 from rfl, ← smul_sub]
        exact Submodule.smul_mem _ _ (pd_lift_spec 𝕜 W r s n x)), map_smul] }

theorem pd_pFun_eq_of (𝕜 : Type) [Field 𝕜] (W : CohFilt 𝕜) (r s n : ℕ)
    (x : ↥(pd_K 𝕜 W r s n)) (z : ↥(pZ 𝕜 W (r+1) s n))
    (hz : x.1 - z.1 ∈ pDen 𝕜 W r s n) :
    pd_pFun 𝕜 W r s n x
      = Submodule.mkQ ((pDen 𝕜 W (r+1) s n).comap (pZ 𝕜 W (r+1) s n).subtype) z :=
  pd_lift_eq_of 𝕜 W r s n x z hz


theorem pd_pFun_eq_zero_of_mem (𝕜 : Type) [Field 𝕜] (W : CohFilt 𝕜) (r s n : ℕ)
    {x : ↥(pd_K 𝕜 W r s n)} (hx : x.1 ∈ pDen 𝕜 W r s n) : pd_pFun 𝕜 W r s n x = 0 := by
  rw [pd_pFun_eq_of 𝕜 W r s n x 0 (by
    show x.1 - (0 : W.C.X n) ∈ pDen 𝕜 W r s n
    rw [sub_zero]; exact hx)]
  exact map_zero _

theorem pd_pFun_eq_of_sub_mem (𝕜 : Type) [Field 𝕜] (W : CohFilt 𝕜) (r s n : ℕ)
    {x x' : ↥(pd_K 𝕜 W r s n)} (h : x.1 - x'.1 ∈ pDen 𝕜 W r s n) :
    pd_pFun 𝕜 W r s n x = pd_pFun 𝕜 W r s n x' := by
  have h0 : pd_pFun 𝕜 W r s n (x - x') = 0 := pd_pFun_eq_zero_of_mem 𝕜 W r s n (by
    show x.1 - x'.1 ∈ pDen 𝕜 W r s n
    exact h)
  have h1 : pd_pFun 𝕜 W r s n x - pd_pFun 𝕜 W r s n x' = 0 := by
    rw [← map_sub]; exact h0
  exact sub_eq_zero.mp h1

theorem pd_pFun_zero_iff (𝕜 : Type) [Field 𝕜] (W : CohFilt 𝕜) (r s n : ℕ)
    (x : ↥(pd_K 𝕜 W r s n)) :
    pd_pFun 𝕜 W r s n x = 0 ↔ x.1 ∈ pDen 𝕜 W r s n ⊔ pDen 𝕜 W (r+1) s n := by
  constructor
  · intro hx
    have hlift : (pd_lift 𝕜 W r s n x : W.C.X n) ∈ pDen 𝕜 W (r+1) s n := by
      have h2 : Submodule.mkQ ((pDen 𝕜 W (r+1) s n).comap (pZ 𝕜 W (r+1) s n).subtype)
          (pd_lift 𝕜 W r s n x) = 0 := hx
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h2
      exact h2
    rw [show x.1 = (x.1 - (pd_lift 𝕜 W r s n x).1)
        + (pd_lift 𝕜 W r s n x).1 from by abel]
    exact Submodule.mem_sup.mpr ⟨x.1 - (pd_lift 𝕜 W r s n x).1, pd_lift_spec 𝕜 W r s n x,
      (pd_lift 𝕜 W r s n x).1, hlift, by rw [sub_add_cancel]⟩
  · intro hx
    obtain ⟨d, hd, z, hz, hdz⟩ := Submodule.mem_sup.mp hx
    have hzz : z ∈ pZ 𝕜 W (r+1) s n := pd_pDen_le_pZ (r+1) s n hz
    have hcomp : x.1 - (⟨z, hzz⟩ : ↥(pZ 𝕜 W (r+1) s n)) ∈ pDen 𝕜 W r s n := by
      show x.1 - z ∈ pDen 𝕜 W r s n
      rw [show x.1 - z = d from by rw [← hdz]; abel]
      exact hd
    have h3 : Submodule.mkQ ((pDen 𝕜 W (r+1) s n).comap (pZ 𝕜 W (r+1) s n).subtype)
        (⟨z, hzz⟩ : ↥(pZ 𝕜 W (r+1) s n)) = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hz
    rw [pd_pFun_eq_of 𝕜 W r s n x ⟨z, hzz⟩ hcomp]
    exact h3

/-! ## 8. The comparison `K ↠ ker d_r` -/

/-- The class of a cycle vanishes iff the cycle lies in the denominator. -/
theorem pd_mkQ_eq_zero_iff (𝕜 : Type) [Field 𝕜] (W : CohFilt 𝕜) (r s n : ℕ)
    (z : ↥(pZ 𝕜 W r s n)) :
    Submodule.mkQ ((pDen 𝕜 W r s n).comap (pZ 𝕜 W r s n).subtype) z = 0
      ↔ z.1 ∈ pDen 𝕜 W r s n := by
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact Iff.rfl

/-- The class map from the preimage of `ker d_r` to `ker d_r ⊆ E_r^s`. -/
noncomputable def pd_Phi (𝕜 : Type) [Field 𝕜] (W : CohFilt 𝕜) (r s n : ℕ) :
    ↥(pd_K 𝕜 W r s n) →ₗ[𝕜] ↥(LinearMap.ker (pD 𝕜 W r s n).hom) :=
  LinearMap.codRestrict (LinearMap.ker (pD 𝕜 W r s n).hom)
    ((Submodule.mkQ ((pDen 𝕜 W r s n).comap (pZ 𝕜 W r s n).subtype)).comp
      (Submodule.inclusion (inf_le_left : pd_K 𝕜 W r s n ≤ pZ 𝕜 W r s n)))
    (fun a => by
      rw [LinearMap.mem_ker]
      show (pD 𝕜 W r s n).hom (Submodule.mkQ ((pDen 𝕜 W r s n).comap (pZ 𝕜 W r s n).subtype)
          (Submodule.inclusion (inf_le_left : pd_K 𝕜 W r s n ≤ pZ 𝕜 W r s n) a)) = 0
      rw [pd_pD_apply r s n (Submodule.inclusion (inf_le_left : pd_K 𝕜 W r s n ≤ pZ 𝕜 W r s n) a)]
      show Submodule.mkQ ((pDen 𝕜 W r (s+r) (n+1)).comap (pZ 𝕜 W r (s+r) (n+1)).subtype)
          (pZmap 𝕜 W r s n
            (Submodule.inclusion (inf_le_left : pd_K 𝕜 W r s n ≤ pZ 𝕜 W r s n) a)) = 0
      exact (pd_mkQ_eq_zero_iff 𝕜 W r (s+r) (n+1) _).mpr (by
        rw [pd_pZmap_apply]
        exact (Submodule.mem_inf.mp a.2).2))

theorem pd_Phi_apply (𝕜 : Type) [Field 𝕜] (W : CohFilt 𝕜) (r s n : ℕ)
    (a : ↥(pd_K 𝕜 W r s n)) :
    (pd_Phi 𝕜 W r s n a : pEraw 𝕜 W r s n)
      = Submodule.mkQ ((pDen 𝕜 W r s n).comap (pZ 𝕜 W r s n).subtype)
          (Submodule.inclusion (inf_le_left : pd_K 𝕜 W r s n ≤ pZ 𝕜 W r s n) a) := rfl

theorem pd_Phi_ker_iff (𝕜 : Type) [Field 𝕜] (W : CohFilt 𝕜) (r s n : ℕ)
    (a : ↥(pd_K 𝕜 W r s n)) :
    pd_Phi 𝕜 W r s n a = 0 ↔ a.1 ∈ pDen 𝕜 W r s n := by
  constructor
  · intro h
    have h1 : Submodule.mkQ ((pDen 𝕜 W r s n).comap (pZ 𝕜 W r s n).subtype)
        (Submodule.inclusion (inf_le_left : pd_K 𝕜 W r s n ≤ pZ 𝕜 W r s n) a) = 0 :=
      congrArg Subtype.val h
    exact (pd_mkQ_eq_zero_iff 𝕜 W r s n _).mp h1
  · intro h
    refine Subtype.ext ?_
    have h2 : Submodule.mkQ ((pDen 𝕜 W r s n).comap (pZ 𝕜 W r s n).subtype)
        (Submodule.inclusion (inf_le_left : pd_K 𝕜 W r s n ≤ pZ 𝕜 W r s n) a) = 0 :=
      (pd_mkQ_eq_zero_iff 𝕜 W r s n _).mpr h
    exact h2

theorem pd_Phi_surj (𝕜 : Type) [Field 𝕜] (W : CohFilt 𝕜) (r s n : ℕ) :
    Function.Surjective (pd_Phi 𝕜 W r s n) := by
  intro y
  obtain ⟨a₀, ha₀⟩ := (Submodule.mkQ_surjective
    ((pDen 𝕜 W r s n).comap (pZ 𝕜 W r s n).subtype)) y.1
  have hda : W.d n a₀.1 ∈ pDen 𝕜 W r (s+r) (n+1) := by
    have h : (pD 𝕜 W r s n).hom (Submodule.mkQ _ a₀) = 0 := by
      rw [ha₀]; exact y.2
    rw [pd_pD_apply r s n a₀] at h
    show W.d n a₀.1 ∈ pDen 𝕜 W r (s+r) (n+1)
    rw [← pd_pZmap_apply r s n a₀]
    exact (pd_mkQ_eq_zero_iff 𝕜 W r (s+r) (n+1) (pZmap 𝕜 W r s n a₀)).mp h
  refine ⟨⟨a₀.1, ⟨a₀.2, hda⟩⟩, ?_⟩
  refine Subtype.ext ?_
  have h2 : (pd_Phi 𝕜 W r s n ⟨a₀.1, ⟨a₀.2, hda⟩⟩ : pEraw 𝕜 W r s n)
      = Submodule.mkQ ((pDen 𝕜 W r s n).comap (pZ 𝕜 W r s n).subtype)
          (Submodule.inclusion (inf_le_left : pd_K 𝕜 W r s n ≤ pZ 𝕜 W r s n)
            ⟨a₀.1, ⟨a₀.2, hda⟩⟩) :=
    pd_Phi_apply 𝕜 W r s n ⟨a₀.1, ⟨a₀.2, hda⟩⟩
  rw [h2]
  rw [show (Submodule.inclusion (inf_le_left : pd_K 𝕜 W r s n ≤ pZ 𝕜 W r s n)
      ⟨a₀.1, ⟨a₀.2, hda⟩⟩ : ↥(pZ 𝕜 W r s n)) = a₀ from Subtype.ext rfl]
  exact ha₀

/-! ## 9. The projection `ker d_r → E_{r+1}` -/
/-- Transport of a cycle along equalities of the filtration index and the cohomological degree. -/
theorem pd_pZ_xcast {r a b m k : ℕ} (h : a = b) (h' : m = k) {x : W.C.X m}
    (hx : x ∈ pZ 𝕜 W r a m) : W.xcast h' x ∈ pZ 𝕜 W r b k := by
  cases h
  refine ⟨pd_transport_mem' (t := a) (h := rfl) h' hx.1, ?_⟩
  show W.d k (W.xcast h' x) ∈ W.F (a + r) (k + 1)
  rw [← pd_xcast_d h' (show m + 1 = k + 1 by omega) x]
  exact pd_transport_mem' (t := a + r) (h := rfl) (show m + 1 = k + 1 by omega) hx.2

/-- The transport of a page along reflexive index equalities is the identity. -/
theorem pd_pEcast_refl (r a m : ℕ) (x : pEraw 𝕜 W r a m) :
    (pEcast 𝕜 W r (rfl : a = a) (rfl : m = m)).hom x = x := rfl

/-- Transport of the class of a cycle along equalities of the indices. -/
theorem pd_pEcast_mkQ {r a b m k : ℕ} (h : a = b) (h' : m = k)
    (x : ↥(pZ 𝕜 W r a m)) (y : ↥(pZ 𝕜 W r b k)) (hy : y.1 = W.xcast h' x.1) :
    (pEcast 𝕜 W r h h').hom
        (Submodule.mkQ ((pDen 𝕜 W r a m).comap (pZ 𝕜 W r a m).subtype) x)
      = Submodule.mkQ ((pDen 𝕜 W r b k).comap (pZ 𝕜 W r b k).subtype) y := by
  cases h
  cases h'
  have hyx : y.1 = x.1 := by
    simpa only [CohFilt.xcast_rfl, LinearMap.id_apply] using hy
  have hxy : x = y := Subtype.ext hyx.symm
  subst hxy
  exact pd_pEcast_refl r a m (Submodule.mkQ ((pDen 𝕜 W r a m).comap (pZ 𝕜 W r a m).subtype) x)

/-- Transport of the class of a cycle, with the transported representative made explicit. -/
theorem pd_pEcast_mkQ' {r a b m k : ℕ} (h : a = b) (h' : m = k)
    (x : ↥(pZ 𝕜 W r a m)) :
    (pEcast 𝕜 W r h h').hom
        (Submodule.mkQ ((pDen 𝕜 W r a m).comap (pZ 𝕜 W r a m).subtype) x)
      = Submodule.mkQ ((pDen 𝕜 W r b k).comap (pZ 𝕜 W r b k).subtype)
          ⟨W.xcast h' x.1, pd_pZ_xcast h h' x.2⟩ :=
  pd_pEcast_mkQ h h' x _ rfl

/-- Cycles with the same underlying element have the same class. -/
theorem pd_mkQ_congr {r s n : ℕ} {x y : ↥(pZ 𝕜 W r s n)} (h : x.1 = y.1) :
    Submodule.mkQ ((pDen 𝕜 W r s n).comap (pZ 𝕜 W r s n).subtype) x
      = Submodule.mkQ ((pDen 𝕜 W r s n).comap (pZ 𝕜 W r s n).subtype) y :=
  congrArg (fun t : ↥(pZ 𝕜 W r s n) =>
    Submodule.mkQ ((pDen 𝕜 W r s n).comap (pZ 𝕜 W r s n).subtype) t) (Subtype.ext h)

/-- Two cycles have the same class iff they differ by an element of the denominator. -/
theorem pd_mkQ_eq_iff (r s n : ℕ) (x y : ↥(pZ 𝕜 W r s n)) :
    Submodule.mkQ ((pDen 𝕜 W r s n).comap (pZ 𝕜 W r s n).subtype) x
      = Submodule.mkQ ((pDen 𝕜 W r s n).comap (pZ 𝕜 W r s n).subtype) y
    ↔ x.1 - y.1 ∈ pDen 𝕜 W r s n := by
  rw [← sub_eq_zero, ← map_sub]
  exact pd_mkQ_eq_zero_iff 𝕜 W r s n (x - y)

/-- The projection `ker d_r → E_{r+1}`, as `pd_pFun` composed with a section of `pd_Phi`. -/
noncomputable def pd_projFun (𝕜 : Type) [Field 𝕜] (W : CohFilt 𝕜) (r s n : ℕ)
    (y : ↥(LinearMap.ker (pD 𝕜 W r s n).hom)) : pEraw 𝕜 W (r+1) s n :=
  pd_pFun 𝕜 W r s n (Function.surjInv (pd_Phi_surj 𝕜 W r s n) y)

theorem pd_projFun_add (𝕜 : Type) [Field 𝕜] (W : CohFilt 𝕜) (r s n : ℕ)
    (y1 y2 : ↥(LinearMap.ker (pD 𝕜 W r s n).hom)) :
    pd_projFun 𝕜 W r s n (y1 + y2) = pd_projFun 𝕜 W r s n y1 + pd_projFun 𝕜 W r s n y2 := by
  have hσ : ∀ y, pd_Phi 𝕜 W r s n
      (Function.surjInv (pd_Phi_surj 𝕜 W r s n) y) = y :=
    fun y => Function.surjInv_eq (pd_Phi_surj 𝕜 W r s n) y
  have hker : ((Function.surjInv (pd_Phi_surj 𝕜 W r s n) (y1 + y2))
      - (Function.surjInv (pd_Phi_surj 𝕜 W r s n) y1
          + Function.surjInv (pd_Phi_surj 𝕜 W r s n) y2)).1 ∈ pDen 𝕜 W r s n := by
    rw [← pd_Phi_ker_iff 𝕜 W r s n _]
    rw [map_sub, map_add, hσ, hσ, hσ, sub_self]
  show pd_pFun 𝕜 W r s n (Function.surjInv (pd_Phi_surj 𝕜 W r s n) (y1 + y2))
      = pd_pFun 𝕜 W r s n (Function.surjInv (pd_Phi_surj 𝕜 W r s n) y1)
        + pd_pFun 𝕜 W r s n (Function.surjInv (pd_Phi_surj 𝕜 W r s n) y2)
  rw [pd_pFun_eq_of_sub_mem 𝕜 W r s n hker, map_add]

theorem pd_projFun_smul (𝕜 : Type) [Field 𝕜] (W : CohFilt 𝕜) (r s n : ℕ)
    (c : 𝕜) (y : ↥(LinearMap.ker (pD 𝕜 W r s n).hom)) :
    pd_projFun 𝕜 W r s n (c • y) = c • pd_projFun 𝕜 W r s n y := by
  have hσ : ∀ y, pd_Phi 𝕜 W r s n
      (Function.surjInv (pd_Phi_surj 𝕜 W r s n) y) = y :=
    fun y => Function.surjInv_eq (pd_Phi_surj 𝕜 W r s n) y
  have hker : ((Function.surjInv (pd_Phi_surj 𝕜 W r s n) (c • y))
      - c • (Function.surjInv (pd_Phi_surj 𝕜 W r s n) y)).1 ∈ pDen 𝕜 W r s n := by
    rw [← pd_Phi_ker_iff 𝕜 W r s n _]
    rw [map_sub, map_smul, hσ, hσ, sub_self]
  show pd_pFun 𝕜 W r s n (Function.surjInv (pd_Phi_surj 𝕜 W r s n) (c • y))
      = c • pd_pFun 𝕜 W r s n (Function.surjInv (pd_Phi_surj 𝕜 W r s n) y)
  rw [pd_pFun_eq_of_sub_mem 𝕜 W r s n hker, map_smul]

/-- The projection `ker d_r → E_{r+1}`. -/
noncomputable def pd_proj (𝕜 : Type) [Field 𝕜] (W : CohFilt 𝕜) (r s n : ℕ) :
    ↥(LinearMap.ker (pD 𝕜 W r s n).hom) →ₗ[𝕜] pEraw 𝕜 W (r+1) s n :=
  { toFun := pd_projFun 𝕜 W r s n
    map_add' := pd_projFun_add 𝕜 W r s n
    map_smul' := pd_projFun_smul 𝕜 W r s n }

theorem pd_proj_eq_of (𝕜 : Type) [Field 𝕜] (W : CohFilt 𝕜) (r s n : ℕ)
    (a : ↥(pd_K 𝕜 W r s n)) :
    pd_proj 𝕜 W r s n (pd_Phi 𝕜 W r s n a) = pd_pFun 𝕜 W r s n a := by
  have hσ : ∀ y, pd_Phi 𝕜 W r s n
      (Function.surjInv (pd_Phi_surj 𝕜 W r s n) y) = y :=
    fun y => Function.surjInv_eq (pd_Phi_surj 𝕜 W r s n) y
  have hker : ((Function.surjInv (pd_Phi_surj 𝕜 W r s n) (pd_Phi 𝕜 W r s n a))
      - a).1 ∈ pDen 𝕜 W r s n := by
    rw [← pd_Phi_ker_iff 𝕜 W r s n _]
    rw [map_sub, hσ, sub_self]
  show pd_pFun 𝕜 W r s n (Function.surjInv (pd_Phi_surj 𝕜 W r s n) (pd_Phi 𝕜 W r s n a))
      = pd_pFun 𝕜 W r s n a
  exact pd_pFun_eq_of_sub_mem 𝕜 W r s n hker

theorem pd_pFun_surj (𝕜 : Type) [Field 𝕜] (W : CohFilt 𝕜) (r s n : ℕ) :
    Function.Surjective (pd_pFun 𝕜 W r s n) := by
  intro v
  obtain ⟨z, hz⟩ := (Submodule.mkQ_surjective
    ((pDen 𝕜 W (r+1) s n).comap (pZ 𝕜 W (r+1) s n).subtype)) v
  have hzK : z.1 ∈ pd_K 𝕜 W r s n := pd_pZ_succ_le_K r s n z.2
  refine ⟨⟨z.1, hzK⟩, ?_⟩
  refine (pd_pFun_eq_of 𝕜 W r s n _ z ?_).trans ?_
  · show (⟨z.1, hzK⟩ : ↥(pd_K 𝕜 W r s n)).1 - z.1 ∈ pDen 𝕜 W r s n
    rw [sub_self]
    exact Submodule.zero_mem _
  · exact hz

theorem pd_proj_surj (𝕜 : Type) [Field 𝕜] (W : CohFilt 𝕜) (r s n : ℕ) (hr : 2 ≤ r) :
    Function.Surjective (pd_proj 𝕜 W r s n) := by
  intro v
  obtain ⟨a, ha⟩ := pd_pFun_surj 𝕜 W r s n v
  exact ⟨pd_Phi 𝕜 W r s n a, by rw [pd_proj_eq_of 𝕜 W r s n a, ha]⟩

/-! ## 10. The projection `ker d_r → E_{r+1}` and the product on the pages -/

/-- The cycle in `Z_r^s` underlying an element of the preimage of `ker d_r`. -/
def pd_cyc (r s n : ℕ) (a : ↥(pd_K 𝕜 W r s n)) : ↥(pZ 𝕜 W r s n) :=
  Submodule.inclusion (inf_le_left : pd_K 𝕜 W r s n ≤ pZ 𝕜 W r s n) a

theorem pd_cyc_val (r s n : ℕ) (a : ↥(pd_K 𝕜 W r s n)) : (pd_cyc r s n a).1 = a.1 := rfl

/-- A cycle of `Z_{r+1}^s` viewed as an element of `Z_r^s`. -/
def pd_cycR (r s n : ℕ) (z : ↥(pZ 𝕜 W (r+1) s n)) : ↥(pZ 𝕜 W r s n) :=
  ⟨z.1, pd_pZ_anti (Nat.le_succ r) le_rfl z.2⟩

theorem pd_cycR_val (r s n : ℕ) (z : ↥(pZ 𝕜 W (r+1) s n)) : (pd_cycR r s n z).1 = z.1 := rfl

/-- The class of `a` in `E_r^s`, expressed through `pd_cyc`. -/
theorem pd_Phi_cyc (r s n : ℕ) (a : ↥(pd_K 𝕜 W r s n)) :
    (pd_Phi 𝕜 W r s n a : pEraw 𝕜 W r s n)
      = Submodule.mkQ ((pDen 𝕜 W r s n).comap (pZ 𝕜 W r s n).subtype) (pd_cyc r s n a) :=
  pd_Phi_apply 𝕜 W r s n a

/-- `B_{r+1}^{s'+r}` in degree `n'+1` is the image under the coboundary of `Z_r^{s'}`. -/
theorem pd_mem_pB_succ_iff {r s' n' : ℕ} {z : W.C.X (n'+1)} :
    z ∈ pB 𝕜 W (r+1) (s'+r) (n'+1) ↔
      z ∈ W.F (s'+r) (n'+1) ∧ ∃ u : W.C.X n', u ∈ W.F s' n' ∧ W.d n' u = z := by
  rw [pd_mem_pB_succ (r := r+1) (s := s'+r) (n := n'),
    show (s'+r) + 1 - (r+1) = s' from by omega]

/-- `D_{r+1}^{s'+r}` is contained in `D_r^{s'+r} + d(Z_r^{s'})`. -/
theorem pd_pDen_succ_le_sup {r s' n' : ℕ} {z : W.C.X (n'+1)}
    (hz : z ∈ pDen 𝕜 W (r+1) (s'+r) (n'+1)) :
    z ∈ pDen 𝕜 W r (s'+r) (n'+1) ⊔ (pZ 𝕜 W r s' n').map (W.d n') := by
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hz
  have haZ : a ∈ pZ 𝕜 W r ((s'+r)+1) (n'+1) := ha
  have haD : a ∈ pDen 𝕜 W r (s'+r) (n'+1) :=
    Submodule.mem_sup.mpr
      ⟨a, pd_pZ_anti (Nat.sub_le r 1) le_rfl haZ, 0, Submodule.zero_mem _, by simp⟩
  have hbB : b ∈ (pZ 𝕜 W r s' n').map (W.d n') := by
    obtain ⟨hF, u, hu, hzdu⟩ := (pd_mem_pB_succ_iff (r := r) (s' := s') (n' := n')).mp hb
    rw [← hzdu]
    exact Submodule.mem_map.mpr ⟨u, ⟨hu, Submodule.mem_comap.mpr (by rwa [hzdu])⟩, rfl⟩
  rw [← hab]
  exact (pDen 𝕜 W r (s'+r) (n'+1) ⊔ (pZ 𝕜 W r s' n').map (W.d n')).add_mem
    (Submodule.mem_sup.mpr ⟨a, haD, 0, Submodule.zero_mem _, by simp⟩)
    (Submodule.mem_sup.mpr ⟨0, Submodule.zero_mem _, b, hbB, by simp⟩)

/-- The image of the coboundary on `Z_r^{s'}` is contained in `D_{r+1}^{s'+r}`. -/
theorem pd_pZmap_mem_pDen_succ {r s' n' : ℕ} {z : W.C.X (n'+1)}
    (hz : z ∈ (pZ 𝕜 W r s' n').map (W.d n')) :
    z ∈ pDen 𝕜 W (r+1) (s'+r) (n'+1) := by
  obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hz
  exact Submodule.mem_sup.mpr
    ⟨0, Submodule.zero_mem _, (W.d n') u,
      (pd_mem_pB_succ_iff (r := r) (s' := s') (n' := n')).mpr ⟨hu.2, u, hu.1, rfl⟩,
      by simp⟩

/-- The denominator of `E_{r+1}^{s'+r}` is `D_r^{s'+r} + d(Z_r^{s'})`. -/
theorem pd_pDen_sup_pZmap {r s' n' : ℕ} :
    pDen 𝕜 W r (s'+r) (n'+1) ⊔ pDen 𝕜 W (r+1) (s'+r) (n'+1)
      = pDen 𝕜 W r (s'+r) (n'+1) ⊔ (pZ 𝕜 W r s' n').map (W.d n') :=
  le_antisymm
    (sup_le le_sup_left fun _ hz => pd_pDen_succ_le_sup hz)
    (sup_le le_sup_left fun z hz => Submodule.mem_sup.mpr
      ⟨0, Submodule.zero_mem _, z, pd_pZmap_mem_pDen_succ hz, by simp⟩)

/-- The image of the incoming differential in `E_r` is `D_r^{s'+r} + d(Z_r^{s'})`. -/
theorem pd_Phi_mem_range_iff (r s' n' : ℕ) (a : ↥(pd_K 𝕜 W r (s'+r) (n'+1))) :
    (∃ w : pEraw 𝕜 W r s' n', (pD 𝕜 W r s' n').hom w
        = (pd_Phi 𝕜 W r (s'+r) (n'+1) a : pEraw 𝕜 W r (s'+r) (n'+1)))
      ↔ a.1 ∈ pDen 𝕜 W r (s'+r) (n'+1) ⊔ (pZ 𝕜 W r s' n').map (W.d n') := by
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨u, hu⟩ := Submodule.mkQ_surjective
      ((pDen 𝕜 W r s' n').comap (pZ 𝕜 W r s' n').subtype) w
    rw [← hu, pd_pD_apply r s' n' u, pd_Phi_cyc r (s'+r) (n'+1) a] at hw
    have hmem : (pZmap 𝕜 W r s' n' u).1 - (pd_cyc r (s'+r) (n'+1) a).1
        ∈ pDen 𝕜 W r (s'+r) (n'+1) :=
      (pd_mkQ_eq_iff r (s'+r) (n'+1) _ _).mp hw
    rw [pd_pZmap_apply r s' n' u, pd_cyc_val] at hmem
    refine Submodule.mem_sup.mpr ⟨a.1 - W.d n' u.1, ?_, W.d n' u.1,
      Submodule.mem_map.mpr ⟨u, u.2, rfl⟩, by abel⟩
    have hneg : -(W.d n' u.1 - a.1) ∈ pDen 𝕜 W r (s'+r) (n'+1) :=
      (pDen 𝕜 W r (s'+r) (n'+1)).neg_mem hmem
    simpa only [neg_sub] using hneg
  · intro h
    obtain ⟨d, hd, y, hy, hdy⟩ := Submodule.mem_sup.mp h
    obtain ⟨u, huZ, rfl⟩ := Submodule.mem_map.mp hy
    refine ⟨Submodule.mkQ ((pDen 𝕜 W r s' n').comap (pZ 𝕜 W r s' n').subtype) ⟨u, huZ⟩, ?_⟩
    rw [pd_pD_apply r s' n' ⟨u, huZ⟩, pd_Phi_cyc r (s'+r) (n'+1) a]
    refine (pd_mkQ_eq_iff r (s'+r) (n'+1) _ _).mpr ?_
    rw [pd_pZmap_apply r s' n' ⟨u, huZ⟩, pd_cyc_val]
    rw [show W.d n' u - a.1 = -d from by rw [← hdy]; abel]
    exact (pDen 𝕜 W r (s'+r) (n'+1)).neg_mem hd

/-- **The kernel of the projection is the image of the incoming differential.** -/
theorem pd_proj_ker (r s n : ℕ) (hr : 2 ≤ r) (s' n' : ℕ) (hs : s' + r = s) (hn : n' + 1 = n)
    (x : ↥(LinearMap.ker (pD 𝕜 W r s n).hom)) :
    pd_proj 𝕜 W r s n x = 0 ↔ ∃ w : pEraw 𝕜 W r s' n',
      (pEcast 𝕜 W r hs hn).hom ((pD 𝕜 W r s' n').hom w) = (x : pEraw 𝕜 W r s n) := by
  revert x
  cases hs
  cases hn
  intro x
  show pd_proj 𝕜 W r (s'+r) (n'+1) x = 0 ↔ ∃ w : pEraw 𝕜 W r s' n',
    (pD 𝕜 W r s' n').hom w = (x : pEraw 𝕜 W r (s'+r) (n'+1))
  set az := Function.surjInv (pd_Phi_surj 𝕜 W r (s'+r) (n'+1)) x
  have hzx : pd_Phi 𝕜 W r (s'+r) (n'+1) az = x :=
    Function.surjInv_eq (pd_Phi_surj 𝕜 W r (s'+r) (n'+1)) x
  have hproj : pd_proj 𝕜 W r (s'+r) (n'+1) x
      = pd_pFun 𝕜 W r (s'+r) (n'+1) az := by
    rw [← hzx]
    exact pd_proj_eq_of 𝕜 W r (s'+r) (n'+1) az
  have hmain : (pd_pFun 𝕜 W r (s'+r) (n'+1) az = 0)
      ↔ az.1 ∈ pDen 𝕜 W r (s'+r) (n'+1) ⊔ (pZ 𝕜 W r s' n').map (W.d n') := by
    rw [pd_pFun_zero_iff 𝕜 W r (s'+r) (n'+1) az,
      pd_pDen_sup_pZmap (r := r) (s' := s') (n' := n')]
  have hL : (pd_proj 𝕜 W r (s'+r) (n'+1) x = 0)
      ↔ (pd_pFun 𝕜 W r (s'+r) (n'+1) az = 0) := by rw [hproj]
  have hR : (∃ w : pEraw 𝕜 W r s' n',
        (pD 𝕜 W r s' n').hom w = (x : pEraw 𝕜 W r (s'+r) (n'+1)))
      ↔ (∃ w : pEraw 𝕜 W r s' n', (pD 𝕜 W r s' n').hom w
          = (pd_Phi 𝕜 W r (s'+r) (n'+1) az : pEraw 𝕜 W r (s'+r) (n'+1))) := by
    rw [show (x : pEraw 𝕜 W r (s'+r) (n'+1))
      = (pd_Phi 𝕜 W r (s'+r) (n'+1) az : pEraw 𝕜 W r (s'+r) (n'+1)) from by rw [hzx]]
  exact (hL.trans hmain).trans ((hR.trans (pd_Phi_mem_range_iff r s' n' az)).symm)

/-- **The Leibniz rule on the pages**, for the product induced by `W.mul`. -/
theorem pd_mul_leib (r s n s' n' : ℕ)
    (e₁ : s+r+s' = s+s'+r) (e₁' : n+1+n' = n+n'+1)
    (e₂ : s+(s'+r) = s+s'+r) (e₂' : n+(n'+1) = n+n'+1)
    (x : pEraw 𝕜 W r s n) (y : pEraw 𝕜 W r s' n') :
    (pD 𝕜 W r (s+s') (n+n')).hom ((pd_mul r s n s' n') x y) =
      (pEcast 𝕜 W r e₁ e₁').hom
          ((pd_mul r (s+r) (n+1) s' n') ((pD 𝕜 W r s n).hom x) y)
      + (-1 : 𝕜)^n •
          (pEcast 𝕜 W r e₂ e₂').hom
            ((pd_mul r s n (s'+r) (n'+1)) x ((pD 𝕜 W r s' n').hom y)) := by
  obtain ⟨x₀, hx₀⟩ := Submodule.mkQ_surjective ((pDen 𝕜 W r s n).comap (pZ 𝕜 W r s n).subtype) x
  obtain ⟨y₀, hy₀⟩ := Submodule.mkQ_surjective ((pDen 𝕜 W r s' n').comap (pZ 𝕜 W r s' n').subtype) y
  rw [← hx₀, ← hy₀]
  set Y₁ : ↥(pZ 𝕜 W r (s+s'+r) (n+n'+1)) :=
    ⟨W.xcast e₁' (pd_mulZ r (s+r) (n+1) s' n' (pZmap 𝕜 W r s n x₀) y₀ : W.C.X ((n+1)+n')),
      pd_pZ_xcast e₁ e₁' (pd_mulZ r (s+r) (n+1) s' n' (pZmap 𝕜 W r s n x₀) y₀).2⟩
  set Y₂ : ↥(pZ 𝕜 W r (s+s'+r) (n+n'+1)) :=
    ⟨W.xcast e₂' (pd_mulZ r s n (s'+r) (n'+1) x₀ (pZmap 𝕜 W r s' n' y₀) : W.C.X (n+(n'+1))),
      pd_pZ_xcast e₂ e₂' (pd_mulZ r s n (s'+r) (n'+1) x₀ (pZmap 𝕜 W r s' n' y₀)).2⟩
  have hL : (pD 𝕜 W r (s+s') (n+n')).hom
        ((pd_mul r s n s' n')
          (Submodule.mkQ ((pDen 𝕜 W r s n).comap (pZ 𝕜 W r s n).subtype) x₀)
          (Submodule.mkQ ((pDen 𝕜 W r s' n').comap (pZ 𝕜 W r s' n').subtype) y₀))
      = Submodule.mkQ ((pDen 𝕜 W r (s+s'+r) (n+n'+1)).comap (pZ 𝕜 W r (s+s'+r) (n+n'+1)).subtype)
          (pZmap 𝕜 W r (s+s') (n+n') (pd_mulZ r s n s' n' x₀ y₀)) := by
    rw [pd_mul_nat r s n s' n' x₀ y₀,
      pd_pD_apply r (s+s') (n+n') (pd_mulZ r s n s' n' x₀ y₀)]
  have hR1 : (pEcast 𝕜 W r e₁ e₁').hom
        ((pd_mul r (s+r) (n+1) s' n')
          ((pD 𝕜 W r s n).hom (Submodule.mkQ ((pDen 𝕜 W r s n).comap (pZ 𝕜 W r s n).subtype) x₀))
          (Submodule.mkQ ((pDen 𝕜 W r s' n').comap (pZ 𝕜 W r s' n').subtype) y₀))
      = Submodule.mkQ ((pDen 𝕜 W r (s+s'+r) (n+n'+1)).comap (pZ 𝕜 W r (s+s'+r) (n+n'+1)).subtype) Y₁ := by
    rw [pd_pD_apply r s n x₀, pd_mul_nat r (s+r) (n+1) s' n' (pZmap 𝕜 W r s n x₀) y₀]
    exact pd_pEcast_mkQ' e₁ e₁' (pd_mulZ r (s+r) (n+1) s' n' (pZmap 𝕜 W r s n x₀) y₀)
  have hR2 : (pEcast 𝕜 W r e₂ e₂').hom
        ((pd_mul r s n (s'+r) (n'+1))
          (Submodule.mkQ ((pDen 𝕜 W r s n).comap (pZ 𝕜 W r s n).subtype) x₀)
          ((pD 𝕜 W r s' n').hom (Submodule.mkQ ((pDen 𝕜 W r s' n').comap (pZ 𝕜 W r s' n').subtype) y₀)))
      = Submodule.mkQ ((pDen 𝕜 W r (s+s'+r) (n+n'+1)).comap (pZ 𝕜 W r (s+s'+r) (n+n'+1)).subtype) Y₂ := by
    rw [pd_pD_apply r s' n' y₀, pd_mul_nat r s n (s'+r) (n'+1) x₀ (pZmap 𝕜 W r s' n' y₀)]
    exact pd_pEcast_mkQ' e₂ e₂' (pd_mulZ r s n (s'+r) (n'+1) x₀ (pZmap 𝕜 W r s' n' y₀))
  have hval : (pZmap 𝕜 W r (s+s') (n+n') (pd_mulZ r s n s' n' x₀ y₀)).1
      - ((Y₁ : ↥(pZ 𝕜 W r (s+s'+r) (n+n'+1))) + (-1:𝕜)^n • Y₂).1 = 0 := by
    show (pZmap 𝕜 W r (s+s') (n+n') (pd_mulZ r s n s' n' x₀ y₀)).1
        - (W.xcast e₁' (pd_mulZ r (s+r) (n+1) s' n' (pZmap 𝕜 W r s n x₀) y₀ : W.C.X ((n+1)+n'))
          + (-1:𝕜)^n • W.xcast e₂' (pd_mulZ r s n (s'+r) (n'+1) x₀ (pZmap 𝕜 W r s' n' y₀)
              : W.C.X (n+(n'+1)))) = 0
    rw [pd_pZmap_apply r (s+s') (n+n') (pd_mulZ r s n s' n' x₀ y₀),
      pd_mulZ_val r s n s' n' x₀ y₀,
      pd_mulZ_val r (s+r) (n+1) s' n' (pZmap 𝕜 W r s n x₀) y₀,
      pd_pZmap_apply r s n x₀,
      pd_mulZ_val r s n (s'+r) (n'+1) x₀ (pZmap 𝕜 W r s' n' y₀),
      pd_pZmap_apply r s' n' y₀,
      W.mul_leib' n n' (x₀ : W.C.X n) (y₀ : W.C.X n'), sub_self]
  have hZ : Submodule.mkQ ((pDen 𝕜 W r (s+s'+r) (n+n'+1)).comap (pZ 𝕜 W r (s+s'+r) (n+n'+1)).subtype)
        (pZmap 𝕜 W r (s+s') (n+n') (pd_mulZ r s n s' n' x₀ y₀))
      = Submodule.mkQ ((pDen 𝕜 W r (s+s'+r) (n+n'+1)).comap (pZ 𝕜 W r (s+s'+r) (n+n'+1)).subtype)
          ((Y₁ : ↥(pZ 𝕜 W r (s+s'+r) (n+n'+1))) + (-1:𝕜)^n • Y₂) :=
    (pd_mkQ_eq_iff r (s+s'+r) (n+n'+1) _ _).mpr (by rw [hval]; exact Submodule.zero_mem _)
  have hsplit : Submodule.mkQ ((pDen 𝕜 W r (s+s'+r) (n+n'+1)).comap (pZ 𝕜 W r (s+s'+r) (n+n'+1)).subtype)
        ((Y₁ : ↥(pZ 𝕜 W r (s+s'+r) (n+n'+1))) + (-1:𝕜)^n • Y₂)
      = Submodule.mkQ ((pDen 𝕜 W r (s+s'+r) (n+n'+1)).comap (pZ 𝕜 W r (s+s'+r) (n+n'+1)).subtype) Y₁
        + (-1:𝕜)^n •
          Submodule.mkQ ((pDen 𝕜 W r (s+s'+r) (n+n'+1)).comap (pZ 𝕜 W r (s+s'+r) (n+n'+1)).subtype) Y₂ := by
    rw [map_add, map_smul]
  have hsum : Submodule.mkQ ((pDen 𝕜 W r (s+s'+r) (n+n'+1)).comap (pZ 𝕜 W r (s+s'+r) (n+n'+1)).subtype) Y₁
        + (-1:𝕜)^n •
          Submodule.mkQ ((pDen 𝕜 W r (s+s'+r) (n+n'+1)).comap (pZ 𝕜 W r (s+s'+r) (n+n'+1)).subtype) Y₂
      = (pEcast 𝕜 W r e₁ e₁').hom
          ((pd_mul r (s+r) (n+1) s' n')
            ((pD 𝕜 W r s n).hom (Submodule.mkQ ((pDen 𝕜 W r s n).comap (pZ 𝕜 W r s n).subtype) x₀))
            (Submodule.mkQ ((pDen 𝕜 W r s' n').comap (pZ 𝕜 W r s' n').subtype) y₀))
        + (-1:𝕜)^n •
          (pEcast 𝕜 W r e₂ e₂').hom
            ((pd_mul r s n (s'+r) (n'+1))
              (Submodule.mkQ ((pDen 𝕜 W r s n).comap (pZ 𝕜 W r s n).subtype) x₀)
              ((pD 𝕜 W r s' n').hom
                (Submodule.mkQ ((pDen 𝕜 W r s' n').comap (pZ 𝕜 W r s' n').subtype) y₀))) := by
    refine Eq.trans (congrArg (fun t => t + (-1:𝕜)^n •
      Submodule.mkQ ((pDen 𝕜 W r (s+s'+r) (n+n'+1)).comap (pZ 𝕜 W r (s+s'+r) (n+n'+1)).subtype) Y₂)
      hR1.symm) ?_
    exact congrArg (fun t => (pEcast 𝕜 W r e₁ e₁').hom
        ((pd_mul r (s+r) (n+1) s' n')
          ((pD 𝕜 W r s n).hom (Submodule.mkQ ((pDen 𝕜 W r s n).comap (pZ 𝕜 W r s n).subtype) x₀))
          (Submodule.mkQ ((pDen 𝕜 W r s' n').comap (pZ 𝕜 W r s' n').subtype) y₀))
      + (-1:𝕜)^n • t) hR2.symm
  exact Eq.trans hL (Eq.trans hZ (Eq.trans hsplit hsum))

/-- **The descent of the product**: the projection `ker d_r → E_{r+1}` is multiplicative. -/
theorem pd_proj_mul (r : ℕ) (hr : 2 ≤ r) (s n s' n' : ℕ)
    (x : ↥(LinearMap.ker (pD 𝕜 W r s n).hom))
    (y : ↥(LinearMap.ker (pD 𝕜 W r s' n').hom))
    (z : ↥(LinearMap.ker (pD 𝕜 W r (s+s') (n+n')).hom))
    (hz : (z : pEraw 𝕜 W r (s+s') (n+n')) = (pd_mul r s n s' n') x y) :
    pd_proj 𝕜 W r (s+s') (n+n') z
      = (pd_mul (r+1) s n s' n') (pd_proj 𝕜 W r s n x) (pd_proj 𝕜 W r s' n' y) := by
  set ax := Function.surjInv (pd_Phi_surj 𝕜 W r s n) x
  set ay := Function.surjInv (pd_Phi_surj 𝕜 W r s' n') y
  set az := Function.surjInv (pd_Phi_surj 𝕜 W r (s+s') (n+n')) z
  have hx : pd_Phi 𝕜 W r s n ax = x := Function.surjInv_eq (pd_Phi_surj 𝕜 W r s n) x
  have hy : pd_Phi 𝕜 W r s' n' ay = y := Function.surjInv_eq (pd_Phi_surj 𝕜 W r s' n') y
  have hzx : pd_Phi 𝕜 W r (s+s') (n+n') az = z :=
    Function.surjInv_eq (pd_Phi_surj 𝕜 W r (s+s') (n+n')) z
  have hmk : Submodule.mkQ ((pDen 𝕜 W r (s+s') (n+n')).comap (pZ 𝕜 W r (s+s') (n+n')).subtype)
        (pd_cyc r (s+s') (n+n') az)
      = Submodule.mkQ ((pDen 𝕜 W r (s+s') (n+n')).comap (pZ 𝕜 W r (s+s') (n+n')).subtype)
        (pd_mulZ r s n s' n' (pd_cyc r s n ax) (pd_cyc r s' n' ay)) := by
    rw [← pd_Phi_cyc r (s+s') (n+n') az, hzx, hz, ← hx, ← hy,
      pd_Phi_cyc r s n ax, pd_Phi_cyc r s' n' ay,
      pd_mul_nat r s n s' n' (pd_cyc r s n ax) (pd_cyc r s' n' ay)]
  have hazD : az.1 - (pd_mulZ r s n s' n' (pd_cyc r s n ax) (pd_cyc r s' n' ay) : W.C.X (n+n'))
      ∈ pDen 𝕜 W r (s+s') (n+n') := by
    have hm := (pd_mkQ_eq_iff r (s+s') (n+n') (pd_cyc r (s+s') (n+n') az)
      (pd_mulZ r s n s' n' (pd_cyc r s n ax) (pd_cyc r s' n' ay))).mp hmk
    simpa only [pd_cyc_val] using hm
  have hA : pd_proj 𝕜 W r (s+s') (n+n') z
      = Submodule.mkQ ((pDen 𝕜 W (r+1) (s+s') (n+n')).comap (pZ 𝕜 W (r+1) (s+s') (n+n')).subtype)
          (pd_lift 𝕜 W r (s+s') (n+n') az) := by
    rw [← hzx]
    exact pd_proj_eq_of 𝕜 W r (s+s') (n+n') az
  have hB : (pd_mul (r+1) s n s' n') (pd_proj 𝕜 W r s n x) (pd_proj 𝕜 W r s' n' y)
      = Submodule.mkQ ((pDen 𝕜 W (r+1) (s+s') (n+n')).comap (pZ 𝕜 W (r+1) (s+s') (n+n')).subtype)
          (pd_mulZ (r+1) s n s' n' (pd_lift 𝕜 W r s n ax) (pd_lift 𝕜 W r s' n' ay)) := by
    rw [← hx, ← hy, pd_proj_eq_of 𝕜 W r s n ax, pd_proj_eq_of 𝕜 W r s' n' ay]
    show (pd_mul (r+1) s n s' n')
        (Submodule.mkQ ((pDen 𝕜 W (r+1) s n).comap (pZ 𝕜 W (r+1) s n).subtype)
          (pd_lift 𝕜 W r s n ax))
        (Submodule.mkQ ((pDen 𝕜 W (r+1) s' n').comap (pZ 𝕜 W (r+1) s' n').subtype)
          (pd_lift 𝕜 W r s' n' ay))
      = Submodule.mkQ ((pDen 𝕜 W (r+1) (s+s') (n+n')).comap (pZ 𝕜 W (r+1) (s+s') (n+n')).subtype)
          (pd_mulZ (r+1) s n s' n' (pd_lift 𝕜 W r s n ax) (pd_lift 𝕜 W r s' n' ay))
    rw [pd_mul_nat (r+1) s n s' n' (pd_lift 𝕜 W r s n ax) (pd_lift 𝕜 W r s' n' ay)]
  have hmem : (pd_lift 𝕜 W r (s+s') (n+n') az : W.C.X (n+n'))
      - (pd_mulZ (r+1) s n s' n' (pd_lift 𝕜 W r s n ax) (pd_lift 𝕜 W r s' n' ay) : W.C.X (n+n'))
      ∈ pDen 𝕜 W (r+1) (s+s') (n+n') := by
    refine pd_pZ_succ_inter_pDen_le r (s+s') (n+n') ⟨?_, ?_⟩
    · exact (pZ 𝕜 W (r+1) (s+s') (n+n')).sub_mem (pd_lift 𝕜 W r (s+s') (n+n') az).2
        (pd_mulZ (r+1) s n s' n' (pd_lift 𝕜 W r s n ax) (pd_lift 𝕜 W r s' n' ay)).2
    · have h1 : (pd_lift 𝕜 W r (s+s') (n+n') az : W.C.X (n+n')) - az.1
          ∈ pDen 𝕜 W r (s+s') (n+n') := by
        simpa only [neg_sub] using
          (pDen 𝕜 W r (s+s') (n+n')).neg_mem (pd_lift_spec 𝕜 W r (s+s') (n+n') az)
      have h3 : (pd_mulZ r s n s' n' (pd_cyc r s n ax) (pd_cyc r s' n' ay) : W.C.X (n+n'))
          - (pd_mulZ (r+1) s n s' n' (pd_lift 𝕜 W r s n ax) (pd_lift 𝕜 W r s' n' ay) : W.C.X (n+n'))
          ∈ pDen 𝕜 W r (s+s') (n+n') := by
        show W.mul n n' (ax : W.C.X n) (ay : W.C.X n')
            - W.mul n n' (pd_lift 𝕜 W r s n ax : W.C.X n) (pd_lift 𝕜 W r s' n' ay : W.C.X n')
            ∈ pDen 𝕜 W r (s+s') (n+n')
        rw [show W.mul n n' (ax : W.C.X n) (ay : W.C.X n')
              - W.mul n n' (pd_lift 𝕜 W r s n ax : W.C.X n) (pd_lift 𝕜 W r s' n' ay : W.C.X n')
              = W.mul n n' ((ax : W.C.X n) - (pd_lift 𝕜 W r s n ax : W.C.X n)) (ay : W.C.X n')
                + W.mul n n' (pd_lift 𝕜 W r s n ax : W.C.X n)
                    ((ay : W.C.X n') - (pd_lift 𝕜 W r s' n' ay : W.C.X n')) from by
          rw [LinearMap.map_sub (W.mul n n') (ax : W.C.X n) (pd_lift 𝕜 W r s n ax : W.C.X n),
            LinearMap.sub_apply,
            LinearMap.map_sub (W.mul n n' (pd_lift 𝕜 W r s n ax : W.C.X n)) (ay : W.C.X n')
              (pd_lift 𝕜 W r s' n' ay : W.C.X n')]
          abel]
        exact (pDen 𝕜 W r (s+s') (n+n')).add_mem
          (pd_pDen_mul_left r s n s' n'
            ⟨(ax : W.C.X n) - (pd_lift 𝕜 W r s n ax : W.C.X n),
              (pZ 𝕜 W r s n).sub_mem (pd_cyc r s n ax).2 (pd_cycR r s n (pd_lift 𝕜 W r s n ax)).2⟩
            (pd_cyc r s' n' ay) (pd_lift_spec 𝕜 W r s n ax))
          (pd_pDen_mul_right r s n s' n' (pd_cycR r s n (pd_lift 𝕜 W r s n ax))
            ⟨(ay : W.C.X n') - (pd_lift 𝕜 W r s' n' ay : W.C.X n'),
              (pZ 𝕜 W r s' n').sub_mem (pd_cyc r s' n' ay).2
                (pd_cycR r s' n' (pd_lift 𝕜 W r s' n' ay)).2⟩
            (pd_lift_spec 𝕜 W r s' n' ay))
      rw [show (pd_lift 𝕜 W r (s+s') (n+n') az : W.C.X (n+n'))
            - (pd_mulZ (r+1) s n s' n' (pd_lift 𝕜 W r s n ax) (pd_lift 𝕜 W r s' n' ay) : W.C.X (n+n'))
          = ((pd_lift 𝕜 W r (s+s') (n+n') az : W.C.X (n+n')) - az.1)
            + (az.1 - (pd_mulZ r s n s' n' (pd_cyc r s n ax) (pd_cyc r s' n' ay) : W.C.X (n+n')))
            + ((pd_mulZ r s n s' n' (pd_cyc r s n ax) (pd_cyc r s' n' ay) : W.C.X (n+n'))
              - (pd_mulZ (r+1) s n s' n' (pd_lift 𝕜 W r s n ax)
                  (pd_lift 𝕜 W r s' n' ay) : W.C.X (n+n'))) from by abel]
      exact (pDen 𝕜 W r (s+s') (n+n')).add_mem
        ((pDen 𝕜 W r (s+s') (n+n')).add_mem h1 hazD) h3
  have hZ : Submodule.mkQ ((pDen 𝕜 W (r+1) (s+s') (n+n')).comap (pZ 𝕜 W (r+1) (s+s') (n+n')).subtype)
        (pd_lift 𝕜 W r (s+s') (n+n') az)
      = Submodule.mkQ ((pDen 𝕜 W (r+1) (s+s') (n+n')).comap (pZ 𝕜 W (r+1) (s+s') (n+n')).subtype)
          (pd_mulZ (r+1) s n s' n' (pd_lift 𝕜 W r s n ax) (pd_lift 𝕜 W r s' n' ay)) :=
    (pd_mkQ_eq_iff (r+1) (s+s') (n+n') _ _).mpr hmem
  exact Eq.trans hA (Eq.trans hZ hB.symm)

/-! ## 11. Assembly -/

/-- **The page data** of the spectral sequence of a filtered cochain complex with a product. -/
theorem pagesData (𝕜 : Type) [Field 𝕜] (W : Work.Pi6.MSS.CohFilt 𝕜) :
    Nonempty (Work.Pi6.MSS.PagesData 𝕜 W) := by
  classical
  exact ⟨{ mulZ := fun r s n s' n' => pd_mulZ r s n s' n'
           mulZ_val := fun r s n s' n' x y => pd_mulZ_val r s n s' n' x y
           mul := fun r s n s' n' => pd_mul r s n s' n'
           mul_nat := fun r s n s' n' x y => pd_mul_nat r s n s' n' x y
           mul_leib := fun r s n s' n' e₁ e₁' e₂ e₂' x y _ =>
             pd_mul_leib r s n s' n' e₁ e₁' e₂ e₂' x y
           proj := fun r s n => pd_proj 𝕜 W r s n
           proj_surj := fun r s n hr => pd_proj_surj 𝕜 W r s n hr
           proj_ker := fun r s n hr s' n' hs hn x =>
             pd_proj_ker (𝕜 := 𝕜) (W := W) r s n hr s' n' hs hn x
           proj_mul := fun r hr s n s' n' x y z hz =>
             pd_proj_mul (𝕜 := 𝕜) (W := W) r hr s n s' n' x y z hz }⟩

end

end Work.Pi6.MSS
