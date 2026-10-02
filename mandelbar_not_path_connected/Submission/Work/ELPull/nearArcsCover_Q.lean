/-
# `nearArcsCover_Q`: the level-5 near-arc cover of the `u`-pair

The rational certificate behind the last region pull-back of the EL area: the angle map
`angMul 5` (`θ ↦ 4⁵ θ mod 1`, the angle action of `F = (Tsq c)^[5] = (Tantibar c)^[10]`)
carries the near arcs of the polygon `[P₀, P_u']` into the near arcs of the polygon
`[P₀, P_u]`, and the boundary pairs accordingly:

* `P₀ = (371/1023, 404/1023)` is fixed by the angle map (`4⁵ · 371/1023 ≡ 371/1023`),
* `P_u' = (u₁', u₁ + 1)` maps to `P_u = (u₀', u₀ + 1)` (the level-1 `u`-pair maps onto the
  `u`-pair),
* the two near arcs `(404/1023, u₁')` and `(u₁ + 1, 371/1023 + 1)` of `[P₀, P_u']` map *into*
  the corresponding near arcs `(404/1023, u₀')` and `(u₀ + 1, 371/1023 + 1)` of `[P₀, P_u]`
  (the image arc is exactly the `4⁵`-scaled arc, and the scaling factor of the lengths is
  `417/1072693248 ↦ 417/1047552` and `45/1072693248 ↦ 45/1047552`).

Everything is exact rational arithmetic; the proof reduces each `Int.fract` to the
unwrapped interval description of the arcs.
-/
import Mathlib
import Submission.Work.ELPull.Cert.Checks
import Submission.Work.ELPull.polyPullback

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Classical Set Function Filter
open scoped Topology

namespace Work.ELPull

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## 1. Two generalities: integral translation of the angle map and of the arcs -/

/-- `angMul m` is invariant under integral translations of the angle. -/
theorem angMul_add_intCast (m : ℕ) (x : ℝ) (k : ℤ) : angMul m (x + k) = angMul m x := by
  have h4 : ((4 : ℝ)) ^ m = ((4 ^ m : ℕ) : ℝ) := by push_cast; ring
  rw [angMul, angMul, h4]
  have h : ((4 ^ m : ℕ) : ℝ) * (x + (k : ℝ))
      = ((4 ^ m : ℕ) : ℝ) * x + ((4 ^ m * k : ℤ) : ℝ) := by
    push_cast; ring
  rw [h, Int.fract_add_intCast]

/-- The arcs are invariant under a common integral translation of both endpoints. -/
theorem InArc_add_intCast_iff (y a b : ℝ) (n : ℤ) : InArc y (a + n) (b + n) ↔ InArc y a b := by
  rw [InArc, InArc, arcLen, arcLen]
  have h1 : y - (a + (n : ℝ)) = y - a - (n : ℝ) := by ring
  have h2 : b + (n : ℝ) - (a + (n : ℝ)) = b - a := by ring
  rw [h1, h2, Int.fract_sub_intCast]

/-- `ccwLift b a = a` when `b` lies in `(a - 1, a]`. -/
theorem ccwLift_eq_right {b a : ℝ} (h : -1 < b - a) (h' : b - a ≤ 0) : ccwLift b a = a := by
  rw [ccwLift,
    show ⌈b - a⌉ = 0 from
      Int.ceil_eq_iff.mpr ⟨by push_cast; linarith, by push_cast; linarith⟩]
  norm_num

/-- `ccwLift b a = a + 1` when `b` lies in `(a, a + 1]`. -/
theorem ccwLift_eq_add_one {b a : ℝ} (h : 0 < b - a) (h' : b - a ≤ 1) : ccwLift b a = a + 1 := by
  rw [ccwLift,
    show ⌈b - a⌉ = 1 from
      Int.ceil_eq_iff.mpr ⟨by push_cast; linarith, by push_cast; linarith⟩]
  norm_num

/-! ## 2. The near arcs of a two-element polygon -/

/-- The first near arc of the polygon `[P, Q]`. -/
theorem nearArc_pair_fst {c : ℂ} {hN : DynB c} (P Q : CoPair hN) :
    nearArc [P, Q] (0 : Fin 2) = (P.b, ccwLift P.b Q.a) := by
  simp [nearArc, nextIdx, List.get_eq_getElem]

/-- The second near arc of the polygon `[P, Q]`. -/
theorem nearArc_pair_snd {c : ℂ} {hN : DynB c} (P Q : CoPair hN) :
    nearArc [P, Q] (1 : Fin 2) = (Q.b, ccwLift Q.b P.a) := by
  simp [nearArc, nextIdx, List.get_eq_getElem]

/-! ## 3. The two near-arc transfers of the certificate (exact rational arithmetic) -/

/-- **First near-arc transfer.**  The angles of `(404/1023, 423625121/1072693248)` are carried
by `angMul 5` into the arc `(404/1023, 414113/1047552)`. -/
theorem InArc_angMul5_Q0 (x : ℝ) (hx : InArc x ((404 : ℝ) / 1023) ((423625121 : ℝ) / 1072693248)) :
    InArc (angMul 5 x) ((404 : ℝ) / 1023) ((414113 : ℝ) / 1047552) := by
  have hlen : arcLen ((404 : ℝ) / 1023) ((423625121 : ℝ) / 1072693248) = 417 / 1072693248 := by
    rw [arcLen, Int.fract_eq_self.mpr (by norm_num)]; norm_num
  have hx2 : Int.fract (x - 404 / 1023)
      < arcLen ((404 : ℝ) / 1023) ((423625121 : ℝ) / 1072693248) := hx.2
  rw [hlen] at hx2
  obtain ⟨δ, k, hδ0, hδ1, hxk⟩ :
      ∃ δ : ℝ, ∃ k : ℤ, 0 < δ ∧ δ < 417 / 1072693248 ∧ x = 404 / 1023 + δ + k :=
    ⟨Int.fract (x - 404 / 1023), ⌊x - 404 / 1023⌋, hx.1, hx2, by
      have h := Int.self_sub_floor (x - 404 / 1023); linarith⟩
  have hang : angMul 5 x = 404 / 1023 + 1024 * δ := by
    rw [hxk, angMul_add_intCast, angMul]
    rw [show (4 : ℝ) ^ 5 = 1024 by norm_num]
    rw [Int.fract_eq_iff]
    exact ⟨by linarith, by linarith, ⟨404, by ring_nf⟩⟩
  rw [hang]
  have h2 : arcLen ((404 : ℝ) / 1023) ((414113 : ℝ) / 1047552) = 417 / 1047552 := by
    rw [arcLen, Int.fract_eq_self.mpr (by norm_num)]; norm_num
  rw [InArc, h2]
  have hfr : Int.fract ((404 / 1023 + 1024 * δ) - 404 / 1023) = 1024 * δ := by
    have hh : (404 / 1023 + 1024 * δ) - 404 / 1023 = 1024 * δ := by ring
    rw [hh, Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
  rw [hfr]
  exact ⟨by linarith, by linarith⟩

/-- **Second near-arc transfer.**  The angles of `(u₁ + 1, 371/1023 + 1)` are carried by
`angMul 5` into the arc `(u₀ + 1, 371/1023 + 1)`, where `u₁ = 389021651/1072693248` and
`u₀ = 379859/1047552`. -/
theorem InArc_angMul5_Q1 (x : ℝ)
    (hx : InArc x ((389021651 : ℝ) / 1072693248 + 1) ((371 : ℝ) / 1023 + 1)) :
    InArc (angMul 5 x) ((379859 : ℝ) / 1047552 + 1) ((371 : ℝ) / 1023 + 1) := by
  have hlen : arcLen ((389021651 : ℝ) / 1072693248 + 1) ((371 : ℝ) / 1023 + 1)
      = 45 / 1072693248 := by
    rw [arcLen, Int.fract_eq_self.mpr (by norm_num)]; norm_num
  have hx2 : Int.fract (x - ((389021651 : ℝ) / 1072693248 + 1))
      < arcLen ((389021651 : ℝ) / 1072693248 + 1) ((371 : ℝ) / 1023 + 1) := hx.2
  rw [hlen] at hx2
  obtain ⟨δ, k, hδ0, hδ1, hxk⟩ :
      ∃ δ : ℝ, ∃ k : ℤ, 0 < δ ∧ δ < 45 / 1072693248 ∧
        x = (389021651 / 1072693248 + 1) + δ + k :=
    ⟨Int.fract (x - ((389021651 : ℝ) / 1072693248 + 1)),
      ⌊x - ((389021651 : ℝ) / 1072693248 + 1)⌋, hx.1, hx2, by
      have h := Int.self_sub_floor (x - ((389021651 : ℝ) / 1072693248 + 1)); linarith⟩
  have hang : angMul 5 x = 379859 / 1047552 + 1024 * δ := by
    rw [hxk, angMul_add_intCast, angMul]
    rw [show (4 : ℝ) ^ 5 = 1024 by norm_num]
    rw [Int.fract_eq_iff]
    exact ⟨by linarith, by linarith, ⟨1395, by ring_nf⟩⟩
  rw [hang]
  rw [show InArc (379859 / 1047552 + 1024 * δ) (379859 / 1047552 + 1) (371 / 1023 + 1)
      ↔ InArc (379859 / 1047552 + 1024 * δ) (379859 / 1047552) (371 / 1023) from by
    have h := InArc_add_intCast_iff (379859 / 1047552 + 1024 * δ) (379859 / 1047552)
      (371 / 1023) 1
    simpa using h]
  have h2 : arcLen ((379859 : ℝ) / 1047552) ((371 : ℝ) / 1023) = 45 / 1047552 := by
    rw [arcLen, Int.fract_eq_self.mpr (by norm_num)]; norm_num
  rw [InArc, h2]
  have hfr : Int.fract ((379859 / 1047552 + 1024 * δ) - 379859 / 1047552) = 1024 * δ := by
    have hh : (379859 / 1047552 + 1024 * δ) - 379859 / 1047552 = 1024 * δ := by ring
    rw [hh, Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
  rw [hfr]
  exact ⟨by linarith, by linarith⟩

/-! ## 4. The statement -/

theorem nearArcsCover_Q {c : ℂ} (hN : DynB c) (P0 Pu Pu' : CoPair hN)
    (hP0 : P0.a = (Cert.A1 : ℝ) ∧ P0.b = (Cert.A2 : ℝ))
    (hPu : Pu.a = (Cert.U0p : ℝ) ∧ Pu.b = (Cert.U0 : ℝ) + 1)
    (hPu' : Pu'.a = (Cert.U1p : ℝ) ∧ Pu'.b = (Cert.U1 : ℝ) + 1) :
    NearArcsCover hN [P0, Pu] [P0, Pu'] 5 := by
  have hA1 : (Cert.A1 : ℝ) = 371 / 1023 := by norm_num [Cert.A1, qq]
  have hA2 : (Cert.A2 : ℝ) = 404 / 1023 := by norm_num [Cert.A2, qq]
  have hU0 : (Cert.U0 : ℝ) = 379859 / 1047552 := by norm_num [Cert.U0, qq]
  have hU0p : (Cert.U0p : ℝ) = 414113 / 1047552 := by norm_num [Cert.U0p, qq]
  have hU1 : (Cert.U1 : ℝ) = 389021651 / 1072693248 := by norm_num [Cert.U1, qq]
  have hU1p : (Cert.U1p : ℝ) = 423625121 / 1072693248 := by norm_num [Cert.U1p, qq]
  -- the four boundary-pair computations
  have hA1f : angMul 5 ((371 : ℝ) / 1023) = Int.fract ((371 : ℝ) / 1023) := by
    have h1 : angMul 5 ((371 : ℝ) / 1023) = 371 / 1023 := by
      rw [angMul, show (4 : ℝ) ^ 5 = 1024 by norm_num, Int.fract_eq_iff]
      exact ⟨by norm_num, by norm_num, ⟨371, by norm_num⟩⟩
    have h2 : Int.fract ((371 : ℝ) / 1023) = 371 / 1023 :=
      Int.fract_eq_self.mpr (by norm_num)
    rw [h1, h2]
  have hA2f : angMul 5 ((404 : ℝ) / 1023) = Int.fract ((404 : ℝ) / 1023) := by
    have h1 : angMul 5 ((404 : ℝ) / 1023) = 404 / 1023 := by
      rw [angMul, show (4 : ℝ) ^ 5 = 1024 by norm_num, Int.fract_eq_iff]
      exact ⟨by norm_num, by norm_num, ⟨404, by norm_num⟩⟩
    have h2 : Int.fract ((404 : ℝ) / 1023) = 404 / 1023 :=
      Int.fract_eq_self.mpr (by norm_num)
    rw [h1, h2]
  have hU1pf : angMul 5 ((423625121 : ℝ) / 1072693248) = Int.fract ((414113 : ℝ) / 1047552) := by
    have h1 : angMul 5 ((423625121 : ℝ) / 1072693248) = 414113 / 1047552 := by
      rw [angMul, show (4 : ℝ) ^ 5 = 1024 by norm_num, Int.fract_eq_iff]
      exact ⟨by norm_num, by norm_num, ⟨404, by norm_num⟩⟩
    have h2 : Int.fract ((414113 : ℝ) / 1047552) = 414113 / 1047552 :=
      Int.fract_eq_self.mpr (by norm_num)
    rw [h1, h2]
  have hU1f : angMul 5 ((389021651 : ℝ) / 1072693248 + 1)
      = Int.fract ((379859 : ℝ) / 1047552 + 1) := by
    have h1 : angMul 5 ((389021651 : ℝ) / 1072693248 + 1) = 379859 / 1047552 := by
      rw [angMul, show (4 : ℝ) ^ 5 = 1024 by norm_num, Int.fract_eq_iff]
      exact ⟨by norm_num, by norm_num, ⟨1395, by norm_num⟩⟩
    have h2 : Int.fract ((379859 : ℝ) / 1047552 + 1) = 379859 / 1047552 := by
      rw [Int.fract_eq_iff]
      exact ⟨by norm_num, by norm_num, ⟨1, by norm_num⟩⟩
    rw [h1, h2]
  refine ⟨?_, ?_⟩
  · -- the boundary pairs
    intro P' hP'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hP'
    rcases hP' with h | h
    · rw [h]
      refine ⟨P0, by simp, ?_, ?_⟩
      · rw [hP0.1, hA1]; exact hA1f
      · rw [hP0.2, hA2]; exact hA2f
    · rw [h]
      refine ⟨Pu, by simp, ?_, ?_⟩
      · rw [hPu'.1, hU1p, hPu.1, hU0p]; exact hU1pf
      · rw [hPu'.2, hU1, hPu.2, hU0]; exact hU1f
  · -- the near arcs
    intro i
    fin_cases i
    · refine ⟨(0 : Fin 2), ?_⟩
      intro x hx
      have hsrc : InArc x ((404 : ℝ) / 1023) ((423625121 : ℝ) / 1072693248) := by
        have h : InArc x P0.b (ccwLift P0.b Pu'.a) := by
          simpa [nearArc, nextIdx, List.get_eq_getElem] using hx
        rw [hP0.2, hA2, hPu'.1, hU1p,
          ccwLift_eq_right (b := (404 : ℝ) / 1023) (a := (423625121 : ℝ) / 1072693248)
            (by norm_num) (by norm_num)] at h
        exact h
      have hgoal : InArc (angMul 5 x) P0.b (ccwLift P0.b Pu.a) := by
        rw [hP0.2, hA2, hPu.1, hU0p,
          ccwLift_eq_right (b := (404 : ℝ) / 1023) (a := (414113 : ℝ) / 1047552)
            (by norm_num) (by norm_num)]
        exact InArc_angMul5_Q0 x hsrc
      simpa [nearArc, nextIdx, List.get_eq_getElem] using hgoal
    · refine ⟨(1 : Fin 2), ?_⟩
      intro x hx
      have hsrc : InArc x ((389021651 : ℝ) / 1072693248 + 1) ((371 : ℝ) / 1023 + 1) := by
        have h : InArc x Pu'.b (ccwLift Pu'.b P0.a) := by
          simpa [nearArc, nextIdx, List.get_eq_getElem] using hx
        rw [hPu'.2, hU1, hP0.1, hA1,
          ccwLift_eq_add_one (b := (389021651 : ℝ) / 1072693248 + 1) (a := (371 : ℝ) / 1023)
            (by norm_num) (by norm_num)] at h
        exact h
      have hgoal : InArc (angMul 5 x) Pu.b (ccwLift Pu.b P0.a) := by
        rw [hPu.2, hU0, hP0.1, hA1,
          ccwLift_eq_add_one (b := (379859 : ℝ) / 1047552 + 1) (a := (371 : ℝ) / 1023)
            (by norm_num) (by norm_num)]
        exact InArc_angMul5_Q1 x hsrc
      simpa [nearArc, nextIdx, List.get_eq_getElem] using hgoal

end Work.ELPull
