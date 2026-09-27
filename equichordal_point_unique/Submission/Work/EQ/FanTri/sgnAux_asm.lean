import Mathlib
import Submission.Work.EQ.FanTri.fan_split_defs
import Submission.Work.EQ.charValDefs
import Submission.Work.EQ.walk_bounds

namespace Work.EQ.FanTri

open Work.EQ

/-- The state reached after reading *all* the letters of `u` from state `0` is `stAux u 0`
(`wstate u t` is defined as the state after the first `t` letters). -/
lemma wstate_self (u : List Bool) : wstate u u.length = stAux u 0 := by
  unfold wstate
  rw [List.take_length]

/-- A block `true^n` read while the walk rests at state `0` has signed weight `1`: every letter
is the principal step, which is stationary at `A₁` and has signed weight `sgW a true 0 = 1`. -/
lemma sgnAux_replicate_true {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (n : ℕ) :
    sgnAux a (List.replicate n true) 0 = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, sgnAux_cons, sgW_true_zero ha0 ha1, one_mul, stp_true_zero]
    exact ih

/-- The state reached by a block of `true` letters read from state `0` is `0` again. -/
lemma stAux_replicate_true_zero (n : ℕ) : stAux (List.replicate n true) 0 = 0 := by
  rw [stAux_replicate_true, Nat.zero_sub]

/-- **The signed weight of an assembled word.**  For `asm L σ = true^{L₀} σ₀ true^{L₁} σ₁ …`
where every trip `τ ∈ σ` returns to state `0` (`wstate τ τ.length = 0`), the signed weight of the
whole word is the product of the signed weights of the trips: the gaps are read while the walk
rests at `0`, where `sgW a true 0 = -dnW a 0 = 1` (`Work.EQ.dnW_zero`, `Work.EQ.sgW_true_zero`).

Route: induction on `σ`; the gap `true^{Lᵢ}` is read from state `0` (all previous trips return),
so it contributes `(sgW a true 0)^{Lᵢ} = 1` (`sgnAux (replicate n true) 0 = 1`, by
`stAux_replicate_true` and `stAux_append`), and the trip `σᵢ` is read from state `0`. -/
theorem sgnAux_asm {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (L : List ℕ) (σ : List (List Bool))
    (hlen : L.length = σ.length + 1) (hcl : ∀ τ ∈ σ, Work.EQ.FanTri.wstate τ τ.length = 0) :
    Work.EQ.sgnAux a (Work.EQ.FanTri.asm L σ) 0
      = (σ.map (fun τ => Work.EQ.sgnAux a τ 0)).prod := by
  induction σ generalizing L with
  | nil =>
    -- `L = [g]`, so the word is the pure gap `true^g`, read from state `0`
    cases L with
    | nil => simp at hlen
    | cons g gs =>
      cases gs with
      | nil => simpa [asm] using sgnAux_replicate_true ha0 ha1 g
      | cons h hs => simp at hlen
  | cons τ ts ih =>
    cases L with
    | nil => simp at hlen
    | cons g gs =>
      have hlen' : gs.length = ts.length + 1 := by simp at hlen; omega
      -- the first trip closes, so the gap after it is read at state `0`
      have hτ : wstate τ τ.length = 0 := hcl τ (by simp)
      have hcl' : ∀ υ ∈ ts, wstate υ υ.length = 0 := fun υ hυ => hcl υ (by simp [hυ])
      have hst : stAux τ 0 = 0 := by rw [← wstate_self]; exact hτ
      have hg : stAux (List.replicate g true) 0 = 0 := stAux_replicate_true_zero g
      have hgr : sgnAux a (List.replicate g true) 0 = 1 := sgnAux_replicate_true ha0 ha1 g
      have ih' := ih gs hlen' hcl'
      -- `asm (g :: gs) (τ :: ts) = true^g ++ τ ++ asm gs ts`
      rw [show asm (g :: gs) (τ :: ts) = (List.replicate g true ++ τ) ++ asm gs ts from rfl,
        List.append_assoc, sgnAux_append, sgnAux_append, hg, hst, hgr,
        one_mul, ih']
      simp

end Work.EQ.FanTri
