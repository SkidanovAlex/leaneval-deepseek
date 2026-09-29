import Mathlib
import Submission.Work.Resample.paDefs
import Submission.Work.Resample.paBasic
import Submission.Work.Compiler.stack_len_le

namespace Work.Resample

/-- **Size of the static table `Pj` of one axis step of the `Ã` program.**

If `prep` is a `WordR` word which consumes the four parameter values `p, α, s, t` (leaving the
remaining value stack untouched) and produces `Pj` on top of the rest, at cost
`Kb * (t+1) * (p+1)^Kb`, then the total size of `Pj` is at most eight times that cost.

The proof is the generic observation that one `Eval` step increases the length of a stack by at
most one (`Work.Compiler.stack_len_le`): the value stack loses the four encodings of `p, α, s, t`
and gains `Pj`, hence `(Pj.map vsz).sum ≤ vsz (.int p) + vsz (.int α) + vsz (.int s) +
vsz (.int t) + Kb * (t+1) * (p+1)^Kb`; the four terms are absorbed into the cost using
`p.size ≤ p`, `α ≤ α^2 < p`, `s < t` and `Kb ≥ 1`, `p ≥ 100`. -/
theorem paTabSz {Kb p α s t : ℕ} {prep : HvdH.Cmd} {Pj : List HvdH.Val}
    (hprep : ∀ (main : HvdH.Cmd) (N : ℕ) (Cm : ℕ → ℕ), Monotone Cm → HvdH.MulBelow main N Cm → Kb * p < N →
      HvdH.WordR main prep
        (fun vs => ∃ rest, vs = HvdH.Val.int p :: HvdH.Val.int α :: HvdH.Val.int s :: HvdH.Val.int t :: rest)
        (fun vs out => ∃ rest, vs = HvdH.Val.int p :: HvdH.Val.int α :: HvdH.Val.int s :: HvdH.Val.int t :: rest ∧ out = Pj ++ rest)
        (fun _ => Kb * (t + 1) * (p + 1) ^ Kb))
    (main : HvdH.Cmd) (N : ℕ) (Cm : ℕ → ℕ) (hmon : Monotone Cm) (hmb : HvdH.MulBelow main N Cm)
    (hN : Kb * p < N) (hKb : 1 ≤ Kb) (hp : 100 ≤ p) (hα : 2 ≤ α) (hαp : α ^ 2 < p)
    (hs : 2 ≤ s) (hst : s < t) :
    (Pj.map HvdH.vsz).sum ≤ 8 * (Kb * (t + 1) * (p + 1) ^ Kb) := by
  -- numerical facts about the parameters
  have ht4 : 4 ≤ t + 1 := by omega
  have hp4 : 4 ≤ p + 1 := by omega
  have hQ : p + 1 ≤ (p + 1) ^ Kb := by
    have h := Nat.pow_le_pow_right (show 0 < p + 1 by omega) hKb
    simpa using h
  have hCp : (t + 1) * (p + 1) ≤ Kb * (t + 1) * (p + 1) ^ Kb := by
    have h1 : 1 * (t + 1) ≤ Kb * (t + 1) := Nat.mul_le_mul_right _ hKb
    have h2 : 1 * (t + 1) * (p + 1) ≤ Kb * (t + 1) * (p + 1) ^ Kb := Nat.mul_le_mul h1 hQ
    simpa using h2
  -- run the word on the four parameter values
  set vs0 : List HvdH.Val :=
    [HvdH.Val.int p, HvdH.Val.int α, HvdH.Val.int s, HvdH.Val.int t] with hvs0
  set st0 : HvdH.State :=
    ⟨fun _ => HvdH.Glyph.eos, fun k => if k = 0 then HvdH.encs vs0 else []⟩ with hst0
  have hst0' : st0.stk 0 = HvdH.encs vs0 := by rw [hst0]; simp
  obtain ⟨out, s', n, hPost, hev, hcost, h0', _⟩ :=
    hprep main N Cm hmon hmb hN vs0 ⟨[], by rw [hvs0]⟩ st0 [] (by simpa using hst0')
  obtain ⟨rest, hvs, hout⟩ := hPost
  have hrest : rest = [] := by simpa [hvs0] using hvs
  have houtPj : out = Pj := by simpa [hrest] using hout
  -- one step changes a stack's length by at most one
  have hlen := Work.Compiler.stack_len_le hev (0 : HvdH.Stk)
  rw [h0', hst0'] at hlen
  have hlen2 : (HvdH.encs out).length ≤ (HvdH.encs vs0).length + n := by simpa using hlen
  have hn : n ≤ Kb * (t + 1) * (p + 1) ^ Kb := hcost
  -- the table is what the stack gained
  have hkey : (Pj.map HvdH.vsz).sum
      ≤ HvdH.vsz (HvdH.Val.int p) + HvdH.vsz (HvdH.Val.int α) + HvdH.vsz (HvdH.Val.int s)
        + HvdH.vsz (HvdH.Val.int t) + n := by
    have h1 : (HvdH.encs Pj).length
        ≤ (HvdH.encs ([HvdH.Val.int p, HvdH.Val.int α, HvdH.Val.int s,
            HvdH.Val.int t] : List HvdH.Val)).length + n := by
      simpa [← houtPj, ← hvs0] using hlen2
    rw [paLenEncS Pj, paLenEncS ([HvdH.Val.int p, HvdH.Val.int α, HvdH.Val.int s,
      HvdH.Val.int t] : List HvdH.Val)] at h1
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at h1
    omega
  -- each consumed parameter value fits into the cost
  have hb1 : HvdH.vsz (HvdH.Val.int p) ≤ Kb * (t + 1) * (p + 1) ^ Kb := by
    rw [paVszIntNat p]
    have h1 : p + 2 ≤ (t + 1) * (p + 1) := by
      have h2 : p + 2 ≤ 4 * (p + 1) := by omega
      have h3 : 4 * (p + 1) ≤ (t + 1) * (p + 1) := Nat.mul_le_mul_right _ ht4
      omega
    have h5 : p.size ≤ p := paSizeLeSelf p
    omega
  have hb2 : HvdH.vsz (HvdH.Val.int α) ≤ Kb * (t + 1) * (p + 1) ^ Kb := by
    rw [paVszIntNat α]
    have hαle : α ≤ p := by
      have h2 : α ≤ α ^ 2 := Nat.le_self_pow (by norm_num : 2 ≠ 0) α
      omega
    have h1 : α + 2 ≤ (t + 1) * (p + 1) := by
      have h2 : α + 2 ≤ 4 * (p + 1) := by omega
      have h3 : 4 * (p + 1) ≤ (t + 1) * (p + 1) := Nat.mul_le_mul_right _ ht4
      omega
    have h5 : α.size ≤ α := paSizeLeSelf α
    omega
  have hb3 : HvdH.vsz (HvdH.Val.int s) ≤ Kb * (t + 1) * (p + 1) ^ Kb := by
    rw [paVszIntNat s]
    have h1 : s + 2 ≤ (t + 1) * (p + 1) := by
      have h2 : s + 2 ≤ t + 1 := by omega
      have h3 : t + 1 ≤ (t + 1) * (p + 1) := Nat.le_mul_of_pos_right _ (by omega)
      omega
    have h5 : s.size ≤ s := paSizeLeSelf s
    omega
  have hb4 : HvdH.vsz (HvdH.Val.int t) ≤ Kb * (t + 1) * (p + 1) ^ Kb := by
    rw [paVszIntNat t]
    have h1 : t + 2 ≤ (t + 1) * (p + 1) := by
      have h2 : t + 2 ≤ 4 * (t + 1) := by omega
      have h3 : 4 * (t + 1) ≤ (t + 1) * (p + 1) := by
        have h4 := Nat.mul_le_mul_left (t + 1) hp4
        simpa [Nat.mul_comm] using h4
      omega
    have h5 : t.size ≤ t := paSizeLeSelf t
    omega
  omega

end Work.Resample
