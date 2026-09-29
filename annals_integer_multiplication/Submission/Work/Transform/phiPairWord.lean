import Mathlib
import Submission.Work.Transform.phiZipDefs
import Submission.Work.Kernel.Raw

/-!
# The pointwise complex-product word `Φ` (paper Lemma 2.4, vector form)

`KernelLib.zipWith` applied to the one-element product word `Work.Transform.cfxMulWord` of
`Submission/Work/Transform/phiAux.lean`: given two `C̃◦`-vectors `pa`, `pb` of the same length `r`
(encoded as `cvecVal pa`, `cvecVal pb` on top of the value stack, with the precision parameter
`int p` below them), it produces a `C̃◦`-vector `ws` of length `r` with

  `2^p * ‖w̃_c - b̃_c * ã_c‖ < 2`   for all `c < r`,

at cost `K * (r * p^2) + K`.  The precision parameter is *kept* below the result.  This is the inner
zip used by `Work.Transform.phiZipWord` (there it is applied block by block through `zipWith`
again).
-/

set_option autoImplicit false

namespace Work.Transform

open HvdH

/-! ## The per-element predicates of the zip -/

/-- Per-element precondition: both values are `cfxVal`s of `C̃◦`. -/
def PhiPairP (p : ℕ) (x y : Val) : Prop :=
  ∃ u v : ℤ × ℤ, x = cfxVal u ∧ y = cfxVal v ∧ inDisc p u ∧ inDisc p v

/-- Per-element postcondition: `z = cfxVal w` with `w ∈ C̃◦` and `2^p ‖w̃ - ṽ * ũ‖ < 2`.  The
output pair `w` is the *first* witness, so that `Classical.choose` of an inhabitant returns it. -/
def PhiPairQ (p : ℕ) (x y z : Val) : Prop :=
  ∃ w : ℤ × ℤ, z = cfxVal w ∧ inDisc p w ∧
    ∃ u v : ℤ × ℤ, x = cfxVal u ∧ y = cfxVal v ∧
      (2 : ℝ) ^ p * ‖fxC p w - fxC p v * fxC p u‖ < 2

/-! ## Cost arithmetic

The zip's cost `r * (c + Kz * (L + 1)) + Kz` with the per-element cost `c = Km * (p+1)^2` of
`cfxMulWord` and the element size bound `L = 2p + 8` of `vsz_cfxVal_le` is within
`K * (r * p^2) + K` with `K = 4 * Km + 12 * Kz + 1`. -/

theorem pairCost (Km Kz r p : ℕ) (hp : 100 ≤ p) (hr : 2 ≤ r) :
    r * (Km * (p + 1) ^ 2 + Kz * (2 * p + 8 + 1)) + Kz
      ≤ (4 * Km + 12 * Kz + 1) * (r * p ^ 2) + (4 * Km + 12 * Kz + 1) := by
  have hsq : (p + 1) ^ 2 ≤ 4 * p ^ 2 := by nlinarith
  have hl : 2 * p + 8 + 1 ≤ 11 * p ^ 2 := by nlinarith
  have h1 : Km * (p + 1) ^ 2 ≤ 4 * Km * p ^ 2 := by
    have := Nat.mul_le_mul_left Km hsq
    nlinarith [this]
  have h2 : Kz * (2 * p + 8 + 1) ≤ 11 * Kz * p ^ 2 := by
    have := Nat.mul_le_mul_left Kz hl
    nlinarith [this]
  have hrp : 1 ≤ r * p ^ 2 := by nlinarith
  have hKz : Kz ≤ Kz * (r * p ^ 2) := by
    have := Nat.mul_le_mul_left Kz hrp
    simpa using this
  have h3 : Km * (p + 1) ^ 2 + Kz * (2 * p + 8 + 1) ≤ (4 * Km + 11 * Kz) * p ^ 2 := by
    nlinarith [h1, h2]
  have h4 : r * (Km * (p + 1) ^ 2 + Kz * (2 * p + 8 + 1)) ≤ r * ((4 * Km + 11 * Kz) * p ^ 2) :=
    Nat.mul_le_mul_left r h3
  have h5 : r * ((4 * Km + 11 * Kz) * p ^ 2) = (4 * Km + 11 * Kz) * (r * p ^ 2) := by ring
  rw [h5] at h4
  nlinarith [h4, hKz, Nat.zero_le Km, Nat.zero_le Kz, Nat.zero_le (r * p ^ 2)]

/-! ## The word -/

theorem phiPairWord : HvdH.KernelLib → HvdH.FxLib →
    ∃ (prog : HvdH.Cmd) (K : ℕ),
    ∀ (main : HvdH.Cmd) (p r : ℕ) (pa pb : List (ℤ × ℤ)) (R : List HvdH.Val),
      pa.length = r → pb.length = r → HvdH.InDiscVec p r pa → HvdH.InDiscVec p r pb →
      100 ≤ p → 2 ≤ r →
      HvdH.WordR main prog
        (fun vs => vs = HvdH.cvecVal pa :: HvdH.cvecVal pb :: HvdH.Val.int p :: R)
        (fun vs out => ∃ ws : List (ℤ × ℤ), out = HvdH.cvecVal ws :: HvdH.Val.int p :: R ∧
          ws.length = r ∧ HvdH.InDiscVec p r ws ∧
          ∀ c < r, (2 : ℝ) ^ p * ‖HvdH.fxC p (ws.getD c (0, 0))
            - HvdH.fxC p (pb.getD c (0, 0)) * HvdH.fxC p (pa.getD c (0, 0))‖ < 2)
        (fun _ => K * (r * p ^ 2) + K) := by
  intro Kl Fl
  obtain ⟨mulP, Km, hmul⟩ := cfxMulWord Kl Fl
  obtain ⟨combq, Kz, hzip⟩ := Kl.zipWith
  refine ⟨combq mulP, 4 * Km + 12 * Kz + 1, ?_⟩
  intro main p r pa pb R hpa hpb hda hdb hp hr
  -- index conversion `r → pa.length`
  have hcl : ∀ i, i < r → i < (pa.map cfxVal).length := by
    intro i hi; rw [List.length_map, hpa]; exact hi
  -- the per-element word: `cfxMulWord`
  have hqzy : ∀ x y, PhiPairP p x y →
      WordR main mulP (fun vs => vs = x :: y :: Val.int (p : ℤ) :: R)
        (fun _ out => ∃ z, out = z :: Val.int (p : ℤ) :: R ∧ PhiPairQ p x y z ∧
          vsz z ≤ 2 * p + 8)
        (fun _ => Km * (p + 1) ^ 2) := by
    intro x y hxy
    obtain ⟨u, v, hx, hy, hu, hv⟩ := hxy
    refine Work.Kernel.WordR_conseq (hmul main p u v R hu hv hp) ?_ ?_ ?_
    · intro _ hvs; rw [hvs, hx, hy]
    · intro vs out hvs hout
      obtain ⟨w, hout', hw, herr⟩ := hout
      exact ⟨cfxVal w, by rw [hout'], ⟨w, rfl, hw, u, v, hx, hy, herr⟩, vsz_cfxVal_le hw⟩
    · intro vs hvs; exact le_refl _
  -- the two memberships the zip needs
  have hPmem : ∀ i < (pa.map cfxVal).length,
      PhiPairP p ((pa.map cfxVal).getD i .nil) ((pb.map cfxVal).getD i .nil) := by
    intro i hi
    have hi' : i < r := by simpa [List.length_map, hpa] using hi
    have hipa : i < pa.length := by rw [hpa]; exact hi'
    have hipb : i < pb.length := by rw [hpb]; exact hi'
    exact ⟨pa.getD i (0, 0), pb.getD i (0, 0), cfxVal_getD hipa, cfxVal_getD hipb,
      inDiscVec_getD hda i hi', inDiscVec_getD hdb i hi'⟩
  have hLmem : ∀ x ∈ (pa.map cfxVal) ++ (pb.map cfxVal), vsz x ≤ 2 * p + 8 := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
      exact vsz_cfxVal_le (hda.2 z hz)
    · obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
      exact vsz_cfxVal_le (hdb.2 z hz)
  have hlen : (pa.map cfxVal).length = (pb.map cfxVal).length := by simp [hpa, hpb]
  have hzip' := hzip main mulP (Val.int (p : ℤ) :: R) (PhiPairP p) (PhiPairQ p)
      (Km * (p + 1) ^ 2) (2 * p + 8) hqzy (pa.map cfxVal) (pb.map cfxVal) hlen hPmem hLmem
  refine Work.Kernel.WordR_conseq hzip' ?_ ?_ ?_
  · intro vs hvs
    rw [hvs]
    rfl
  · -- extraction of the integer pairs `W : Fin r → ℤ × ℤ` from the value list `zs`
    intro vs out hvs hout
    obtain ⟨zs, hout1, hzlen, hQz⟩ := hout
    have hzr : zs.length = r := by rw [hzlen, List.length_map, hpa]
    classical
    let W : Fin r → ℤ × ℤ := fun i => (hQz (i : ℕ) (hcl i i.isLt)).choose
    have hWz : ∀ i : Fin r, zs.getD (i : ℕ) Val.nil = cfxVal (W i) := by
      intro i; exact (hQz (i : ℕ) (hcl i i.isLt)).choose_spec.1
    have hWd : ∀ i : Fin r, inDisc p (W i) := by
      intro i; exact (hQz (i : ℕ) (hcl i i.isLt)).choose_spec.2.1
    have hWu : ∀ i : Fin r, ∃ u v : ℤ × ℤ,
        (pa.map cfxVal).getD (i : ℕ) .nil = cfxVal u ∧
        (pb.map cfxVal).getD (i : ℕ) .nil = cfxVal v ∧
        (2 : ℝ) ^ p * ‖fxC p (W i) - fxC p v * fxC p u‖ < 2 := by
      intro i; exact (hQz (i : ℕ) (hcl i i.isLt)).choose_spec.2.2
    have hmap : (List.ofFn W).map cfxVal = zs := by
      apply List.ext_getElem
      · simp [List.length_ofFn, hzr]
      · intro i h1 h2
        have h3 : i < r := by simpa [hzr] using h2
        have h4 : ((List.ofFn W).map cfxVal)[i] = cfxVal (W ⟨i, h3⟩) := by
          rw [List.getElem_map (h := h1),
            List.getElem_ofFn (h := by simpa [List.length_ofFn] using h3)]
        rw [h4]
        rw [← List.getD_eq_getElem zs Val.nil h2]
        exact (hWz ⟨i, h3⟩).symm
    refine ⟨List.ofFn W, ?_, ?_, ?_, ?_⟩
    · rw [hout1]
      congr 1
      show ofList zs = ofList ((List.ofFn W).map cfxVal)
      rw [hmap]
    · simp [List.length_ofFn]
    · constructor
      · simp [List.length_ofFn]
      · intro z hz
        rw [List.mem_ofFn] at hz
        obtain ⟨i, rfl⟩ := hz
        exact hWd i
    · -- the pointwise error bound
      intro c hc
      have hWc : (List.ofFn W).getD c (0, 0) = W ⟨c, hc⟩ := by
        rw [List.getD_eq_getElem _ _ (by simpa [List.length_ofFn] using hc)]
        exact List.getElem_ofFn (h := by simpa [List.length_ofFn] using hc)
      obtain ⟨u, v, hu, hv, herr⟩ := hWu ⟨c, hc⟩
      rw [hWc]
      have hupa : u = pa.getD c (0, 0) := by
        have h1 := cfxVal_getD (l := pa) (i := c) (by rw [hpa]; exact hc)
        rw [hu] at h1
        exact cfxVal_injective h1
      have hvpb : v = pb.getD c (0, 0) := by
        have h1 := cfxVal_getD (l := pb) (i := c) (by rw [hpb]; exact hc)
        rw [hv] at h1
        exact cfxVal_injective h1
      rw [hupa, hvpb] at herr
      exact herr
  · intro _vs _hvs
    show (pa.map cfxVal).length * (Km * (p + 1) ^ 2 + Kz * (2 * p + 8 + 1)) + Kz
      ≤ (4 * Km + 12 * Kz + 1) * (r * p ^ 2) + (4 * Km + 12 * Kz + 1)
    rw [List.length_map, hpa]
    exact pairCost Km Kz r p hp hr

end Work.Transform
