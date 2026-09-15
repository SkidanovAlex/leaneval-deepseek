import Mathlib
import Submission.Commons.Combinatorics.Additive.Gowers.gvn_weighted
import Submission.Commons.Combinatorics.Additive.AP.sum_phiC_cover

open scoped BigOperators

namespace Commons.Combinatorics.Additive.Gowers

open Commons.Combinatorics.Additive.AP (sum_phiC_cover)

/-! ## The general linear reparametrisation `phiC`

For an injective `c : Fin k → ZMod p` with `c 0 = 0`, the reparametrisation
`φ_i(y) = ∑_t (1 - c_i / c_{t+1}) y_t` writes the `k`-term AP `x + c_i * r` with
`x = ∑_t y_t`, `r = -∑_t y_t / c_{t+1}`.  This file proves the stage-`0` endpoint of the
weighted Green–Tao quantity for this reparametrisation, the companion of `Jw_last_phiC`. -/

private noncomputable def phiC {p : ℕ} {k : ℕ} (c : Fin k → ZMod p) (i : Fin k)
    (y : Fin (k-1) → ZMod p) : ZMod p :=
  ∑ t : Fin (k-1), (1 - c i * (c ⟨t.val+1, by omega⟩)⁻¹) * y t

private noncomputable def wsigC {p : ℕ} {k : ℕ} (h : Fin (k-1) → ZMod p)
    (ω : Fin (k-1) → Bool) : ZMod p :=
  ∑ j : Fin (k-1), (if ω j then (1 : ZMod p) else 0) * h j

private noncomputable def wtauC {p : ℕ} {k : ℕ} (c : Fin k → ZMod p)
    (h : Fin (k-1) → ZMod p) (ω : Fin (k-1) → Bool) : ZMod p :=
  ∑ j : Fin (k-1), (if ω j then (1 : ZMod p) else 0) * h j * (c ⟨j.val+1, by omega⟩)⁻¹

private noncomputable def wvtxC {p : ℕ} {k : ℕ} (c : Fin k → ZMod p) (g ν : ZMod p → ℝ)
    (x s : ZMod p) (h : Fin (k-1) → ZMod p) (ω : Fin (k-1) → Bool) : ℝ :=
  g (x + wsigC h ω) * ∏ i : Fin (k-1), Real.sqrt (ν (x + wsigC h ω
    - c ⟨1 + i.val, by omega⟩ * (s + wtauC c h ω)))

private noncomputable def wintC {p : ℕ} {k : ℕ} (c : Fin k → ZMod p) (g ν : ZMod p → ℝ)
    (v y' : Fin (k-1) → ZMod p) : ℝ :=
  ∏ ω : Fin (k-1) → Bool,
    (g (∑ j : Fin (k-1), (if ω j then y' j else v j))
      * ∏ i : Fin (k-1), Real.sqrt (ν (phiC c ⟨1 + i.val, by omega⟩
          (fun j => if ω j then y' j else v j))))

/-- Distribution identity: `∑_t (1 - D B_t) u_t = ∑_t u_t - D ∑_t u_t B_t`. -/
private lemma sum_sub_mul {p : ℕ} {n : ℕ} (D : ZMod p) (B u : Fin n → ZMod p) :
    (∑ t, (1 - D * B t) * u t) = (∑ t, u t) - D * (∑ t, u t * B t) := by
  have h : ∀ t, (1 - D * B t) * u t = u t - D * (u t * B t) := by intro t; ring
  rw [Finset.sum_congr rfl (fun t _ => h t), Finset.sum_sub_distrib, ← Finset.mul_sum]

/-- `φ_i` at a vertex `v + ω·h` of the Boolean cube. -/
private lemma phiC_vertex {p : ℕ} {k : ℕ} (c : Fin k → ZMod p)
    (v h : Fin (k-1) → ZMod p) (ω : Fin (k-1) → Bool) (i : Fin k) :
    phiC c i (fun j => if ω j then h j + v j else v j)
      = (∑ t : Fin (k-1), v t) + wsigC h ω
        - c i * ((∑ t : Fin (k-1), v t * (c ⟨t.val+1, by omega⟩)⁻¹) + wtauC c h ω) := by
  rw [phiC, wsigC, wtauC]
  have hsplit : ∀ t : Fin (k-1),
      (1 - c i * (c ⟨t.val+1, by omega⟩)⁻¹) * (if ω t then h t + v t else v t)
      = (1 - c i * (c ⟨t.val+1, by omega⟩)⁻¹) * v t
        + (1 - c i * (c ⟨t.val+1, by omega⟩)⁻¹) * (if ω t then h t else 0) := by
    intro t
    cases hω : ω t <;> simp [hω, mul_add, add_comm, add_left_comm, add_assoc]
  rw [Finset.sum_congr rfl (fun t _ => hsplit t), Finset.sum_add_distrib]
  rw [sum_sub_mul (c i) (fun t => (c ⟨t.val+1, by omega⟩)⁻¹) v,
      sum_sub_mul (c i) (fun t => (c ⟨t.val+1, by omega⟩)⁻¹)
        (fun t => if ω t then h t else 0)]
  have hu : (∑ t : Fin (k-1), (if ω t then h t else 0))
      = ∑ t : Fin (k-1), (if ω t then (1 : ZMod p) else 0) * h t :=
    Finset.sum_congr rfl (fun t _ => by by_cases ht : ω t <;> simp [ht])
  have huB : (∑ t : Fin (k-1), (if ω t then h t else 0) * (c ⟨t.val+1, by omega⟩)⁻¹)
      = ∑ t : Fin (k-1), (if ω t then (1 : ZMod p) else 0) * h t * (c ⟨t.val+1, by omega⟩)⁻¹ :=
    Finset.sum_congr rfl (fun t _ => by by_cases ht : ω t <;> simp [ht])
  rw [hu, huB]
  ring

/-- The `Fin 1` product at stage `0` for `φ_0`: since `c 0 = 0`, `φ_0` is the plain sum. -/
private lemma prod_fin_one_phiC {p : ℕ} {k : ℕ} (c : Fin k → ZMod p)
    (hk : 1 ≤ k) (hc0 : c ⟨0, by omega⟩ = 0)
    (g : Fin k → ZMod p → ℝ) (u : Fin (k-1) → ZMod p) :
    (∏ i : Fin 1, g ⟨i.val, by omega⟩ (phiC c ⟨i.val, by omega⟩ u))
      = g ⟨0, by omega⟩ (∑ j, u j) := by
  rw [Fintype.prod_unique]
  have h0 : ((default : Fin 1) : ℕ) = 0 := rfl
  have hidx : (⟨(default : Fin 1).val, by omega⟩ : Fin k) = (⟨0, by omega⟩ : Fin k) := Fin.ext h0
  rw [hidx]
  congr 1
  rw [phiC]
  apply Finset.sum_congr rfl; intro t _
  rw [hc0, zero_mul, sub_zero, one_mul]

/-- Sum of the coordinates of the cube vertex `v + ω·h`. -/
private lemma sum_vertexC {p : ℕ} {k : ℕ} (v h : Fin (k-1) → ZMod p) (ω : Fin (k-1) → Bool) :
    (∑ j : Fin (k-1), (if ω j then h j + v j else v j))
      = (∑ j : Fin (k-1), v j) + wsigC h ω := by
  rw [wsigC, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro j _
  by_cases hω : ω j = true
  · simp only [if_pos hω, one_mul]; ring
  · simp only [if_neg hω, zero_mul, add_zero]

/-- The stage-`0` integrand at a translated cube vertex, in the coordinates
`x = ∑ v`, `s = ∑ v / c_{t+1}`. -/
private lemma wintC_shift {p : ℕ} {k : ℕ} (c : Fin k → ZMod p) (g ν : ZMod p → ℝ)
    (v h : Fin (k-1) → ZMod p) :
    wintC c g ν v (h + v)
      = ∏ ω : Fin (k-1) → Bool,
          wvtxC c g ν (∑ t : Fin (k-1), v t)
            (∑ t : Fin (k-1), v t * (c ⟨t.val+1, by omega⟩)⁻¹) h ω := by
  rw [wintC]
  apply Finset.prod_congr rfl; intro ω _
  rw [wvtxC]
  congr 1
  · congr 1
    simpa only [Pi.add_apply] using sum_vertexC v h ω
  · apply Finset.prod_congr rfl; intro i _
    congr 1
    congr 1
    simp only [Pi.add_apply]
    rw [phiC_vertex c v h ω ⟨1 + i.val, by omega⟩]

/-- The sum over the cube variables of the stage-`0` integrand is the weighted cube sum. -/
private lemma wintC_sum {p : ℕ} [Fact p.Prime] {k : ℕ} (hk : 3 ≤ k)
    (c : Fin k → ZMod p) (hc : Function.Injective c) (hc0 : c ⟨0, by omega⟩ = 0)
    (g ν : ZMod p → ℝ) :
    (∑ v : Fin (k-1) → ZMod p, ∑ y' : Fin (k-1) → ZMod p, wintC c g ν v y')
      = (p:ℝ)^(k-3) * (∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p, ∑ s : ZMod p,
          ∏ ω : Fin (k-1) → Bool, wvtxC c g ν x s h ω) := by
  have hstep1 : (∑ v : Fin (k-1) → ZMod p, ∑ y' : Fin (k-1) → ZMod p, wintC c g ν v y')
      = (∑ v : Fin (k-1) → ZMod p, ∑ h : Fin (k-1) → ZMod p, wintC c g ν v (h + v)) := by
    apply Finset.sum_congr rfl; intro v _
    exact GVNW.cube_shift (p:=p) (fun y' : Fin (k-1) → ZMod p => wintC c g ν v y') v
  have hstep2 : (∑ v : Fin (k-1) → ZMod p, ∑ h : Fin (k-1) → ZMod p, wintC c g ν v (h + v))
      = (∑ h : Fin (k-1) → ZMod p, ∑ v : Fin (k-1) → ZMod p,
          ∏ ω : Fin (k-1) → Bool,
            wvtxC c g ν (∑ t : Fin (k-1), v t)
              (∑ t : Fin (k-1), v t * (c ⟨t.val+1, by omega⟩)⁻¹) h ω) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro h _
    apply Finset.sum_congr rfl; intro v _
    exact wintC_shift c g ν v h
  have hstep3 : (∑ h : Fin (k-1) → ZMod p, ∑ v : Fin (k-1) → ZMod p,
        ∏ ω : Fin (k-1) → Bool,
          wvtxC c g ν (∑ t : Fin (k-1), v t)
            (∑ t : Fin (k-1), v t * (c ⟨t.val+1, by omega⟩)⁻¹) h ω)
      = (p:ℝ)^(k-3) * (∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p, ∑ s : ZMod p,
          ∏ ω : Fin (k-1) → Bool, wvtxC c g ν x s h ω) := by
    rw [show (∑ h : Fin (k-1) → ZMod p, ∑ v : Fin (k-1) → ZMod p,
          ∏ ω : Fin (k-1) → Bool,
            wvtxC c g ν (∑ t : Fin (k-1), v t)
              (∑ t : Fin (k-1), v t * (c ⟨t.val+1, by omega⟩)⁻¹) h ω)
        = (∑ h : Fin (k-1) → ZMod p,
            (p:ℝ)^(k-3) * ∑ q : ZMod p × ZMod p,
              ∏ ω : Fin (k-1) → Bool, wvtxC c g ν q.1 q.2 h ω) from by
      apply Finset.sum_congr rfl; intro h _
      exact sum_phiC_cover (p:=p) hk c hc hc0
        (fun x s => ∏ ω : Fin (k-1) → Bool, wvtxC c g ν x s h ω)]
    rw [← Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl; intro h _
    rw [Fintype.sum_prod_type]
  rw [hstep1, hstep2, hstep3]

/-- The arithmetic of the stage-`0` endpoint. -/
private lemma arith_zeroC {p : ℕ} {k : ℕ} (hk : 3 ≤ k) (hpne : (p:ℝ) ≠ 0) (W : ℝ) :
    ((p:ℝ)^(k-1) * (p:ℝ)^(k-1))⁻¹ * ((p:ℝ)^(k-3) * W) = ((p:ℝ)^(k+1))⁻¹ * W := by
  have hkey : (p:ℝ)^(k-1) * (p:ℝ)^(k-1) = (p:ℝ)^(k-3) * (p:ℝ)^(k+1) := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  rw [hkey, mul_inv]
  field_simp

/-- The stage-`0` quantity, written with the integrand `wintC` in the cube coordinates. -/
private lemma Jw_zero_phiC_wint {p : ℕ} [Fact p.Prime] {k : ℕ} (hk : 1 ≤ k)
    (c : Fin k → ZMod p) (hc0 : c ⟨0, by omega⟩ = 0) (f : Fin k → ZMod p → ℝ)
    (ν : ZMod p → ℝ) :
    GVNW.Jw (ZMod p) k (phiC c) f ν 0 (by omega)
      = GVNgen.av (fun v : Fin (k-1) → ZMod p => GVNgen.av (fun y' : Fin (k-1) → ZMod p =>
          wintC c (f ⟨0, by omega⟩) ν v y')) := by
  rw [GVNW.Jw_zero (X := ZMod p) (k := k) hk (phiC c) f ν (by omega)]
  apply GVNgen.av_congr; intro v
  apply GVNgen.av_congr; intro y'
  rw [wintC]
  apply Finset.prod_congr rfl; intro ω _
  rw [prod_fin_one_phiC (k := k) c hk hc0 f (fun j => if ω j then y' j else v j)]
  rfl

theorem Jw_zero_phiC {p : ℕ} [Fact p.Prime] {k : ℕ} (hk : 3 ≤ k) (hkp : k ≤ p)
    (c : Fin k → ZMod p) (hc : Function.Injective c) (hc0 : c ⟨0, by omega⟩ = 0)
    (f : Fin k → ZMod p → ℝ) (ν : ZMod p → ℝ) :
    GVNW.Jw (ZMod p) k (fun i y => ∑ t : Fin (k-1), (1 - c i * (c ⟨t.val+1, by omega⟩)⁻¹) * y t)
        f ν 0 (by omega)
      = ((p:ℝ)^(k+1))⁻¹ *
        (∑ h : Fin (k-1) → ZMod p, ∑ x : ZMod p, ∑ s : ZMod p,
          ∏ ω : Fin (k-1) → Bool,
            (f ⟨0, by omega⟩ (x + ∑ j : Fin (k-1), (if ω j then (1:ZMod p) else 0) * h j)
             * ∏ i : Fin (k-1), Real.sqrt (ν (x + ∑ j : Fin (k-1), (if ω j then (1:ZMod p) else 0) * h j
                - c ⟨1 + i.val, by omega⟩
                  * (s + ∑ j : Fin (k-1), (if ω j then (1:ZMod p) else 0) * h j
                      * (c ⟨j.val+1, by omega⟩)⁻¹))))) := by
  have hk1 : 1 ≤ k := by omega
  have hpne : (p:ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [show (fun i y => ∑ t : Fin (k-1), (1 - c i * (c ⟨t.val+1, by omega⟩)⁻¹) * y t)
      = phiC c from by
    funext i y; exact (phiC.eq_1 c i y).symm]
  rw [Jw_zero_phiC_wint (p:=p) hk1 c hc0 f ν]
  have hcard : (Fintype.card ((Fin (k-1) → ZMod p) × (Fin (k-1) → ZMod p)) : ℝ)
      = (p:ℝ)^(k-1) * (p:ℝ)^(k-1) := by
    rw [Fintype.card_prod, Nat.cast_mul, GVNW.card_fun_zmod (p:=p) (k-1)]
  rw [GVNgen.av_prod, GVNgen.av, Fintype.sum_prod_type, hcard]
  rw [wintC_sum (p:=p) hk c hc hc0 (f ⟨0, by omega⟩) ν]
  simp only [wvtxC, wsigC, wtauC]
  exact arith_zeroC (p:=p) (k:=k) hk hpne _

end Commons.Combinatorics.Additive.Gowers
