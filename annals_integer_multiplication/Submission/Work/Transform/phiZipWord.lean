import Mathlib
import Submission.Work.Transform.phiAux
import Submission.Work.Transform.phiZipDefs
import Submission.Work.Transform.phiPairWord
import Submission.Work.Transform.phiZExtract

namespace Work.Transform

open HvdH

/-- Pointwise-product phase of paper Prop 3.5's `T̃` (see `Work.Transform.phiWord`): on `R`-arrays
`a`, `b` of `M` blocks of length `r`, zip the two block lists (`KernelLib.zipWith`), each pair of
blocks being combined coefficient by coefficient (`KernelLib.zipWith` again, with the one-element
product word `Work.Transform.cfxMulWord`, i.e. `KernelLib.pick 2` then `FxLib.mulS`).  The parameter
`int p` is *kept* below the result (so that this is valid for every `M`, including `M = 0`; the
caller, who has `1 ≤ M`, erases it afterwards).  The output `us` carries the pointwise products with
error `< 2` in the `2^p`-scaled norm; cost `K * (M*r*p^2) + K` (at `M = 0` this is the constant `K`,
which is what the empty zips cost). -/
theorem phiZipWord : HvdH.KernelLib → HvdH.IntLib → HvdH.FxLib →
    ∃ (prog : HvdH.Cmd) (K : ℕ),
    ∀ (main : HvdH.Cmd) (p r M : ℕ) (a b : List (List (ℤ × ℤ))) (R : List HvdH.Val),
      a.length = M → b.length = M → HvdH.InDiscArr p M r a → HvdH.InDiscArr p M r b →
      100 ≤ p → 2 ≤ r →
      HvdH.WordR main prog
        (fun vs => vs = HvdH.rarrVal a :: HvdH.rarrVal b :: HvdH.Val.int p :: R)
        (fun vs out => ∃ us : List (List (ℤ × ℤ)), out = HvdH.rarrVal us :: HvdH.Val.int p :: R ∧
          us.length = M ∧ HvdH.InDiscArr p M r us ∧ (∀ i < M, (us.getD i []).length = r) ∧
          ∀ i < M, ∀ c < r, (2 : ℝ) ^ p * ‖HvdH.fxC p ((us.getD i []).getD c (0, 0))
            - HvdH.fxC p ((b.getD i []).getD c (0, 0)) * HvdH.fxC p ((a.getD i []).getD c (0, 0))‖ < 2)
        (fun _ => K * ((M * r) * p ^ 2) + K) := by
  intro Kl Il Fl
  obtain ⟨progB, KB, hB⟩ := phiPairWord Kl Fl
  obtain ⟨combq, Kz, hzip⟩ := Kl.zipWith
  refine ⟨combq progB, 2 * KB + 401 * Kz + 1, ?_⟩
  intro main p r M a b R ha hb hda hdb hp hr
  -- the per-block word: `phiPairWord`, with the element size bound `L = 200 (r p² + 1)`
  have hqzy : ∀ x y, PhiZP p r x y →
      WordR main progB (fun vs => vs = x :: y :: Val.int (p : ℤ) :: R)
        (fun _ out => ∃ z, out = z :: Val.int (p : ℤ) :: R ∧ PhiZQ p r x y z ∧
          vsz z ≤ 200 * (r * p ^ 2 + 1))
        (fun _ => KB * (r * p ^ 2) + KB) := by
    intro x y hxy
    obtain ⟨pa, pb, hx, hy, hpa, hpb⟩ := hxy
    refine Work.Kernel.WordR_conseq (hB main p r pa pb R hpa.1 hpb.1 hpa hpb hp hr) ?_ ?_ ?_
    · intro _ hvs; rw [hvs, hx, hy]
    · intro vs out hvs hout
      obtain ⟨ws, hout', hwl, hwd, herr⟩ := hout
      exact ⟨cvecVal ws, by rw [hout'], ⟨ws, pa, pb, rfl, hx, hy, hwd, herr⟩,
        vsz_cvecVal_le hwd hp⟩
    · intro vs hvs; exact le_refl _
  -- the three side conditions of `KernelLib.zipWith`
  have hPmem : ∀ i < (a.map cvecVal).length,
      PhiZP p r ((a.map cvecVal).getD i .nil) ((b.map cvecVal).getD i .nil) := by
    intro i hi
    have hiM : i < M := by simpa [List.length_map, ha] using hi
    exact ⟨a.getD i [], b.getD i [], cvecVal_getD (by rw [ha]; exact hiM),
      cvecVal_getD (by rw [hb]; exact hiM),
      (inDiscArr_iff ha).mp hda i hiM, (inDiscArr_iff hb).mp hdb i hiM⟩
  have hLmem : ∀ x ∈ (a.map cvecVal) ++ (b.map cvecVal), vsz x ≤ 200 * (r * p ^ 2 + 1) := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx
      exact vsz_cvecVal_le (hda.2 w hw) hp
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx
      exact vsz_cvecVal_le (hdb.2 w hw) hp
  have hlen : (a.map cvecVal).length = (b.map cvecVal).length := by simp [ha, hb]
  have hzip' := hzip main progB (Val.int (p : ℤ) :: R) (PhiZP p r) (PhiZQ p r)
      (KB * (r * p ^ 2) + KB) (200 * (r * p ^ 2 + 1)) hqzy (a.map cvecVal) (b.map cvecVal)
      hlen hPmem hLmem
  refine Work.Kernel.WordR_conseq hzip' ?_ ?_ ?_
  · intro vs hvs; rw [hvs]; rfl
  · -- read the result back as an `R`-array of coefficient vectors
    intro vs out hvs hout
    obtain ⟨zs, hout1, hzlen, hQz⟩ := hout
    have hzM : zs.length = M := by rw [hzlen, List.length_map, ha]
    have hQz' : ∀ i < M, PhiZQ p r ((a.map cvecVal).getD i .nil)
        ((b.map cvecVal).getD i .nil) (zs.getD i .nil) := by
      intro i hi
      exact hQz i (by simpa [List.length_map, ha] using hi)
    obtain ⟨us, hus, huslen, husdisc, huslenr, huserr⟩ := phiZExtract ha hb hzM hQz'
    exact ⟨us, by rw [hout1, hus], huslen, husdisc, huslenr, huserr⟩
  · -- cost
    intro _vs _hvs
    show (a.map cvecVal).length * ((KB * (r * p ^ 2) + KB) + Kz * (200 * (r * p ^ 2 + 1) + 1))
      + Kz ≤ (2 * KB + 401 * Kz + 1) * ((M * r) * p ^ 2) + (2 * KB + 401 * Kz + 1)
    rw [List.length_map, ha]
    exact phiZipCost KB Kz M r p hp hr

end Work.Transform
