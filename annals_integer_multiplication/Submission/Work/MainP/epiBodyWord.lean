import Mathlib
import Submission.Work.MainP.crtLabDefs
import Submission.Work.Kernel.Raw

/-!
# `epiBodyWord`: pulling the label out of a `prp` pair

Given a word `up` that unpacks a `cons a b` into `a :: b` on the value stack, a word `sw` that
swaps the top two values, and a word `dp` that drops the top value, the composite `up ; sw ; dp`
turns the single value `prp v E = cons (int v) (ofList E)` on top of a stack `rest` into
`int v :: rest`, at cost `Ku + Ks * L + Kd * (L + 1)` whenever `vsz (prp v E) ≤ L`.

The proof is a direct chain of the three `WordR` specifications, all sharing the same frame `R`
(the intermediate outputs are full stacks, so the raw content below never changes), together with
the two size estimates `vsz (int v) + vsz (ofList E) + 1 = vsz (prp v E) ≤ L` (the cost of the
swap) and `vsz (ofList E) ≤ L` (the cost of the drop; note that the value dropped is the *second*
component of the pair `prp v E`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.MainP

open HvdH

theorem epiBodyWord (hK : HvdH.KernelLib) {main : HvdH.Cmd} {up sw dp : HvdH.Cmd} {Ku Ks Kd L : ℕ}
    (hup : HvdH.WordR main up (fun vs => ∃ a b r, vs = HvdH.Val.cons a b :: r)
      (fun vs out => ∃ a b r, vs = HvdH.Val.cons a b :: r ∧ out = a :: b :: r) (fun _ => Ku))
    (hsw : HvdH.WordR main sw (fun vs => 2 ≤ vs.length)
      (fun vs out => ∃ a b r, vs = a :: b :: r ∧ out = b :: a :: r)
      (fun vs => Ks * (HvdH.vsz (vs.getD 0 HvdH.Val.nil) + HvdH.vsz (vs.getD 1 HvdH.Val.nil) + 1)))
    (hdp : HvdH.WordR main dp (fun vs => vs ≠ [])
      (fun vs out => ∃ v r, vs = v :: r ∧ out = r)
      (fun vs => Kd * (HvdH.vsz (vs.headD HvdH.Val.nil) + 1))) :
    ∀ (rest : List HvdH.Val) (v : ℤ) (E : List HvdH.Val), HvdH.vsz (Work.MainP.prp v E) ≤ L →
      HvdH.WordR main (up.seq (sw.seq dp)) (fun vs => vs = Work.MainP.prp v E :: rest)
        (fun _ out => ∃ y, out = y :: rest ∧ y = HvdH.Val.int v ∧ HvdH.vsz y ≤ L)
        (fun _ => Ku + Ks * L + Kd * (L + 1)) := by
  intro rest v E hE vs hpre s R hR
  -- `vsz (prp v E) = vsz (int v) + vsz (ofList E) + 1 ≤ L`.
  have hL : HvdH.vsz (HvdH.Val.int v) + HvdH.vsz (HvdH.ofList E) + 1 ≤ L := by
    have h := hE
    rw [Work.MainP.prp, Work.MainP.vsz_cons] at h
    exact h
  have hofL : HvdH.vsz (HvdH.ofList E) ≤ L := by omega
  have hintL : HvdH.vsz (HvdH.Val.int v) ≤ L := by omega
  rw [hpre] at hR
  -- Step 1: `up` splits the pair `prp v E = cons (int v) (ofList E)`.
  obtain ⟨out₁, s₁, n₁, hQ₁, he₁, hn₁, hstk₁, hoth₁⟩ :=
    hup (Work.MainP.prp v E :: rest) ⟨HvdH.Val.int v, HvdH.ofList E, rest, rfl⟩ s R hR
  obtain ⟨a₁, b₁, r₁, hvs₁, hout₁⟩ := hQ₁
  have h1 : a₁ = HvdH.Val.int v ∧ b₁ = HvdH.ofList E ∧ r₁ = rest := by
    have h := hvs₁
    simp only [Work.MainP.prp, List.cons.injEq, HvdH.Val.cons.injEq] at h
    exact ⟨h.1.1.symm, h.1.2.symm, h.2.symm⟩
  have hout₁' : out₁ = HvdH.Val.int v :: HvdH.ofList E :: rest := by
    rw [hout₁, h1.1, h1.2.1, h1.2.2]
  -- Step 2: `sw` exchanges the two components.
  obtain ⟨out₂, s₂, n₂, hQ₂, he₂, hn₂, hstk₂, hoth₂⟩ :=
    hsw out₁ (by rw [hout₁']; simp) s₁ R hstk₁
  obtain ⟨a₂, b₂, r₂, hmid₂, hout₂⟩ := hQ₂
  have h2 : a₂ = HvdH.Val.int v ∧ b₂ = HvdH.ofList E ∧ r₂ = rest := by
    have h := hmid₂
    rw [hout₁'] at h
    simp only [List.cons.injEq] at h
    exact ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩
  have hout₂' : out₂ = HvdH.ofList E :: HvdH.Val.int v :: rest := by
    rw [hout₂, h2.1, h2.2.1, h2.2.2]
  -- Step 3: `dp` discards the (now leading) state component.
  obtain ⟨out₃, s₃, n₃, hQ₃, he₃, hn₃, hstk₃, hoth₃⟩ :=
    hdp out₂ (by rw [hout₂']; simp) s₂ R hstk₂
  obtain ⟨v₃, r₃, hmid₃, hout₃⟩ := hQ₃
  have h3 : v₃ = HvdH.ofList E ∧ r₃ = HvdH.Val.int v :: rest := by
    have h := hmid₃
    rw [hout₂'] at h
    simp only [List.cons.injEq] at h
    exact ⟨h.1.symm, h.2.symm⟩
  have hout₃' : out₃ = HvdH.Val.int v :: rest := by rw [hout₃, h3.2]
  -- The sizes seen by the two later calls, evaluated on the concrete intermediate stacks.
  have hget₀ : out₁.getD 0 HvdH.Val.nil = HvdH.Val.int v := by rw [hout₁']; rfl
  have hget₁ : out₁.getD 1 HvdH.Val.nil = HvdH.ofList E := by rw [hout₁']; rfl
  have hhead : out₂.headD HvdH.Val.nil = HvdH.ofList E := by rw [hout₂']; rfl
  refine ⟨out₃, s₃, n₁ + (n₂ + n₃), ⟨HvdH.Val.int v, hout₃', rfl, hintL⟩,
    Eval.seq he₁ (Eval.seq he₂ he₃), ?_, hstk₃, ?_⟩
  · have hc₁ : n₁ ≤ Ku := hn₁
    have hc₂ : n₂ ≤ Ks * L := by
      have h : n₂ ≤ Ks * (HvdH.vsz (out₁.getD 0 HvdH.Val.nil)
        + HvdH.vsz (out₁.getD 1 HvdH.Val.nil) + 1) := hn₂
      rw [hget₀, hget₁] at h
      exact le_trans h (Nat.mul_le_mul_left Ks hL)
    have hc₃ : n₃ ≤ Kd * (L + 1) := by
      have h : n₃ ≤ Kd * (HvdH.vsz (out₂.headD HvdH.Val.nil) + 1) := hn₃
      rw [hhead] at h
      exact le_trans h (Nat.mul_le_mul_left Kd (Nat.succ_le_succ hofL))
    show n₁ + (n₂ + n₃) ≤ Ku + Ks * L + Kd * (L + 1)
    omega
  · intro k hk
    rw [hoth₃ k hk, hoth₂ k hk, hoth₁ k hk]

end Work.MainP
