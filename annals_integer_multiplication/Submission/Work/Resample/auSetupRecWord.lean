import Mathlib
import Submission.Work.Resample.auSetupDefs
import Submission.Work.Kernel.encodeNatBits

/-!
# The record word of the resampling setup (`Work.Resample.auSetupRecWord`)

One value-level operation: `cons (int g) w ↦ cons (flag g) (cons (int g) w)`, where `flag g` is
`nil` for `g = 0` and `(nil . nil)` otherwise.  The program duplicates the value, takes it apart
with `unconsV`, drops the tail, tests the integer with `ifZero` and rebuilds the `cons` with the
flag on top.  The whole thing costs a constant multiple of `vsz r + 1`.
-/

namespace Work.Resample

open HvdH

/-! ## Small size facts (the `ConvR`/`IntLib` copies live in heavier modules) -/

private theorem auEncodeNat_length (n : ℕ) : (Computability.encodeNat n).length = n.size := by
  rw [Work.Kernel.encodeNatBits, Nat.size_eq_bits_len]

private theorem auVszInt (z : ℤ) : vsz (Val.int z) = isz z := by
  simp only [vsz, Val.enc, List.length_cons, List.length_append, List.length_nil,
    List.length_map, auEncodeNat_length, isz]

private theorem auVszCons (a b : Val) : vsz (Val.cons a b) = vsz a + vsz b + 1 := by
  simp only [vsz, Val.enc, List.length_cons, List.length_append]

private theorem auVszNil : vsz Val.nil = 1 := by
  simp [vsz, Val.enc]

private theorem auVszFlag : vsz (Val.cons Val.nil Val.nil) = 3 := by
  simp [vsz, Val.enc]

private theorem auSetupRecFun_cons (g : ℤ) (w : Val) :
    auSetupRecFun (Val.cons (Val.int g) w) = Val.cons (auSetupFlag g) (Val.cons (Val.int g) w) :=
  rfl

private theorem auSetupFlag_zero : auSetupFlag 0 = Val.nil := by
  unfold auSetupFlag
  rw [if_pos rfl]

private theorem auSetupFlag_ne (g : ℤ) (h : g ≠ 0) :
    auSetupFlag g = Val.cons Val.nil Val.nil := by
  unfold auSetupFlag
  rw [if_neg h]

/-! ## The composition laws of `KernelLib`, with implicit arguments -/

private theorem auSeq (hk : HvdH.KernelLib) {main p q : Cmd} {P P' : List Val → Prop}
    {Q Q' : List Val → List Val → Prop} {C C' B : List Val → ℕ}
    (h₁ : WordR main p P Q C) (h₂ : WordR main q P' Q' C')
    (hmid : ∀ vs mid, P vs → Q vs mid → P' mid ∧ C' mid ≤ B vs) :
    WordR main (.seq p q) P (fun vs out => ∃ mid, Q vs mid ∧ Q' mid out)
      (fun vs => C vs + B vs) :=
  hk.seq main p q P Q C P' Q' C' B h₁ h₂ hmid

private theorem auConseq (hk : HvdH.KernelLib) {main p : Cmd} {P P' : List Val → Prop}
    {Q Q' : List Val → List Val → Prop} {C C' : List Val → ℕ}
    (h : WordR main p P Q C) (hP : ∀ vs, P' vs → P vs)
    (hQ : ∀ vs out, P' vs → Q vs out → Q' vs out) (hC : ∀ vs, P' vs → C vs ≤ C' vs) :
    WordR main p P' Q' C' :=
  hk.conseq main p P P' Q Q' C C' h hP hQ hC

/-- Chain a step with a single-list pre- and post-condition to a step whose post only depends
on the output. -/
private theorem auChain (hk : HvdH.KernelLib) {main p q : Cmd} {a b : List Val}
    {R : List Val → Prop} {K₁ K₂ : ℕ}
    (h₁ : WordR main p (fun vs => vs = a) (fun _ out => out = b) (fun _ => K₁))
    (h₂ : WordR main q (fun vs => vs = b) (fun _ out => R out) (fun _ => K₂)) :
    WordR main (.seq p q) (fun vs => vs = a) (fun _ out => R out) (fun _ => K₁ + K₂) := by
  refine hk.conseq main (.seq p q) (fun vs => vs = a) (fun vs => vs = a)
    (fun vs out => ∃ mid, mid = b ∧ R out) (fun _ out => R out)
    (fun vs => K₁ + K₂) (fun vs => K₁ + K₂)
    (hk.seq main p q (fun vs => vs = a) (fun _ out => out = b) (fun _ => K₁)
      (fun vs => vs = b) (fun _ out => R out) (fun _ => K₂) (fun _ => K₂) h₁ h₂
      (fun vs mid hP hQ => ⟨hQ, le_rfl⟩))
    ?_ ?_ ?_
  · intro vs h; exact h
  · intro vs out h hQ; obtain ⟨mid, hm, ho⟩ := hQ; exact ho
  · intro vs h; exact le_rfl

/-- The arithmetic of the final cost comparison. -/
private theorem auSetupCostLe (Kd Kuc Kiz Kdr Kps Kcs G W R Mc : ℕ)
    (hR : R = G + W + 1) (hMc : Mc ≤ Kdr * (W + 1) + (4 * Kps + Kcs)) :
    ((Kd * (R + 1) + Kuc) + (Kiz * (G + 1) + Mc))
      ≤ (Kd + Kuc + Kiz + Kdr + (4 * Kps + Kcs)) * (R + 1) := by
  subst hR
  nlinarith [hMc]

theorem auSetupRecWord (hk : HvdH.KernelLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (r : HvdH.Val) (rest : List HvdH.Val),
      (∃ (g : ℤ) (w : HvdH.Val), r = HvdH.Val.cons (.int g) w) →
      HvdH.WordR main prog (fun vs => vs = r :: rest)
        (fun vs out => out = Work.Resample.auSetupRecFun r :: rest)
        (fun vs => K * (HvdH.vsz r + 1)) := by
  obtain ⟨dupP, Kd, hdup⟩ := hk.dup
  obtain ⟨ucP, Kuc, huc⟩ := hk.unconsV
  obtain ⟨drP, Kdr, hdr⟩ := hk.drop
  obtain ⟨psP, Kps, hps⟩ := hk.pushVal
  obtain ⟨csP, Kcs, hcs⟩ := hk.consV
  obtain ⟨izC, Kiz, hiz⟩ := hk.ifZero
  let q1 : Cmd := .seq (.seq drP (psP Val.nil)) csP
  let q2 : Cmd := .seq (.seq drP (psP (Val.cons Val.nil Val.nil))) csP
  let inner : Cmd := izC q1 q2
  let prog : Cmd := .seq (.seq dupP ucP) inner
  let K : ℕ := Kd + Kuc + Kiz + Kdr + (4 * Kps + Kcs)
  refine ⟨prog, K, ?_⟩
  intro main r rest hr
  obtain ⟨g, w, hg⟩ := hr
  let c1 : ℕ := Kdr * (vsz w + 1) + (4 * Kps + Kcs)
  -- step 1: duplicate the record
  have h1 : WordR main dupP (fun vs => vs = r :: rest) (fun _ out => out = r :: r :: rest)
      (fun _ => Kd * (vsz r + 1)) := by
    refine auConseq hk (hdup main) ?_ ?_ ?_
    · intro vs h; rw [h]; simp
    · intro vs out h hQ
      obtain ⟨v, l, hv, hout⟩ := hQ
      rw [h] at hv
      obtain ⟨hvr, hlr⟩ := List.cons.inj hv
      rw [← hvr, ← hlr] at hout
      exact hout
    · intro vs h; rw [h]; simp only [List.headD_cons, le_rfl]
  -- step 2: take the record apart
  have h2 : WordR main ucP (fun vs => vs = r :: r :: rest)
      (fun _ out => out = Val.int g :: w :: r :: rest) (fun _ => Kuc) := by
    refine auConseq hk (huc main) ?_ ?_ ?_
    · intro vs h
      rw [h, hg]
      exact ⟨Val.int g, w, Val.cons (Val.int g) w :: rest, rfl⟩
    · intro vs out h hQ
      obtain ⟨a, b, l, hv, hout⟩ := hQ
      rw [h, hg] at hv
      obtain ⟨hv1, hv2⟩ := List.cons.inj hv
      obtain ⟨ha, hb⟩ := Val.cons.inj hv1.symm
      rw [ha, hb, ← hv2] at hout
      rw [hg]
      exact hout
    · intro vs h; exact le_rfl
  -- the two branches of the flag test: drop the tail, push the flag, rebuild the `cons`
  have hq1 : WordR main q1 (fun vs => vs = w :: r :: rest)
      (fun _ out => out = Val.cons Val.nil r :: rest) (fun _ => c1) := by
    have hdrop : WordR main drP (fun vs => vs = w :: r :: rest)
        (fun _ out => out = r :: rest) (fun _ => Kdr * (vsz w + 1)) := by
      refine auConseq hk (hdr main) ?_ ?_ ?_
      · intro vs h; rw [h]; simp
      · intro vs out h hQ
        obtain ⟨v, l, hv, hout⟩ := hQ
        rw [h] at hv
        obtain ⟨_, hv2⟩ := List.cons.inj hv
        rw [← hv2] at hout
        exact hout
      · intro vs h; rw [h]; simp only [List.headD_cons, le_rfl]
    have hpush : WordR main (psP Val.nil) (fun vs => vs = r :: rest)
        (fun _ out => out = Val.nil :: r :: rest) (fun _ => Kps * (vsz Val.nil + 1)) := by
      refine auConseq hk (hps main Val.nil) ?_ ?_ ?_
      · intro vs h; trivial
      · intro vs out h hQ; rw [h] at hQ; exact hQ
      · intro vs h; simp only [le_rfl]
    have hcons : WordR main csP (fun vs => vs = Val.nil :: r :: rest)
        (fun _ out => out = Val.cons Val.nil r :: rest) (fun _ => Kcs) := by
      refine auConseq hk (hcs main) ?_ ?_ ?_
      · intro vs h; rw [h]; simp
      · intro vs out h hQ
        obtain ⟨a, b, l, hv, hout⟩ := hQ
        rw [h] at hv
        obtain ⟨hv1, hv2⟩ := List.cons.inj hv
        obtain ⟨hv1a, hv1b⟩ := List.cons.inj hv2
        rw [← hv1, ← hv1a, ← hv1b] at hout
        exact hout
      · intro vs h; simp only [le_rfl]
    refine auConseq hk (auChain hk (auChain hk hdrop hpush) hcons) ?_ ?_ ?_
    · intro vs h; exact h
    · intro vs out h hQ; exact hQ
    · intro vs h
      show (Kdr * (vsz w + 1) + Kps * (vsz Val.nil + 1)) + Kcs
        ≤ Kdr * (vsz w + 1) + (4 * Kps + Kcs)
      rw [auVszNil]
      nlinarith
  have hq2 : WordR main q2 (fun vs => vs = w :: r :: rest)
      (fun _ out => out = Val.cons (Val.cons Val.nil Val.nil) r :: rest) (fun _ => c1) := by
    have hdrop : WordR main drP (fun vs => vs = w :: r :: rest)
        (fun _ out => out = r :: rest) (fun _ => Kdr * (vsz w + 1)) := by
      refine auConseq hk (hdr main) ?_ ?_ ?_
      · intro vs h; rw [h]; simp
      · intro vs out h hQ
        obtain ⟨v, l, hv, hout⟩ := hQ
        rw [h] at hv
        obtain ⟨_, hv2⟩ := List.cons.inj hv
        rw [← hv2] at hout
        exact hout
      · intro vs h; rw [h]; simp only [List.headD_cons, le_rfl]
    have hpush : WordR main (psP (Val.cons Val.nil Val.nil)) (fun vs => vs = r :: rest)
        (fun _ out => out = Val.cons Val.nil Val.nil :: r :: rest)
        (fun _ => Kps * (vsz (Val.cons Val.nil Val.nil) + 1)) := by
      refine auConseq hk (hps main (Val.cons Val.nil Val.nil)) ?_ ?_ ?_
      · intro vs h; trivial
      · intro vs out h hQ; rw [h] at hQ; exact hQ
      · intro vs h; simp only [le_rfl]
    have hcons : WordR main csP (fun vs => vs = Val.cons Val.nil Val.nil :: r :: rest)
        (fun _ out => out = Val.cons (Val.cons Val.nil Val.nil) r :: rest) (fun _ => Kcs) := by
      refine auConseq hk (hcs main) ?_ ?_ ?_
      · intro vs h; rw [h]; simp
      · intro vs out h hQ
        obtain ⟨a, b, l, hv, hout⟩ := hQ
        rw [h] at hv
        obtain ⟨hv1, hv2⟩ := List.cons.inj hv
        obtain ⟨hv1a, hv1b⟩ := List.cons.inj hv2
        rw [← hv1, ← hv1a, ← hv1b] at hout
        exact hout
      · intro vs h; simp only [le_rfl]
    refine auConseq hk (auChain hk (auChain hk hdrop hpush) hcons) ?_ ?_ ?_
    · intro vs h; exact h
    · intro vs out h hQ; exact hQ
    · intro vs h
      show (Kdr * (vsz w + 1) + Kps * (vsz (Val.cons Val.nil Val.nil) + 1)) + Kcs
        ≤ Kdr * (vsz w + 1) + (4 * Kps + Kcs)
      rw [auVszFlag]
      nlinarith
  -- step 3: the flag test
  have hz : WordR main inner (fun vs => vs = Val.int g :: w :: r :: rest)
      (fun _ out => (g = 0 → out = Val.cons Val.nil r :: rest) ∧
        (g ≠ 0 → out = Val.cons (Val.cons Val.nil Val.nil) r :: rest))
      (fun _ => Kiz * (isz g + 1) + max c1 c1) :=
    hiz main q1 q2 g (w :: r :: rest) (fun out => out = Val.cons Val.nil r :: rest)
      (fun out => out = Val.cons (Val.cons Val.nil Val.nil) r :: rest) c1 c1
      (fun _ => hq1) (fun _ => hq2)
  have hbase : WordR main (.seq (.seq dupP ucP) inner) (fun vs => vs = r :: rest)
      (fun _ out => (g = 0 → out = Val.cons Val.nil r :: rest) ∧
        (g ≠ 0 → out = Val.cons (Val.cons Val.nil Val.nil) r :: rest))
      (fun _ => (Kd * (vsz r + 1) + Kuc) + (Kiz * (isz g + 1) + max c1 c1)) :=
    auChain hk (auChain hk h1 h2) hz
  by_cases hg0 : g = 0
  · refine auConseq hk hbase ?_ ?_ ?_
    · intro vs h; exact h
    · intro vs out h hc
      have hfun : auSetupRecFun r = Val.cons Val.nil r := by
        rw [hg, auSetupRecFun_cons, hg0, auSetupFlag_zero]
      rw [hc.1 hg0, hfun]
    · intro vs h
      have hR : vsz r = vsz (Val.int g) + vsz w + 1 := by rw [hg, auVszCons]
      rw [← auVszInt g]
      exact auSetupCostLe Kd Kuc Kiz Kdr Kps Kcs (vsz (Val.int g)) (vsz w) (vsz r)
        (max c1 c1) hR (le_of_eq (max_self c1))
  · refine auConseq hk hbase ?_ ?_ ?_
    · intro vs h; exact h
    · intro vs out h hc
      have hfun : auSetupRecFun r = Val.cons (Val.cons Val.nil Val.nil) r := by
        rw [hg, auSetupRecFun_cons, auSetupFlag_ne g hg0]
      rw [hc.2 hg0, hfun]
    · intro vs h
      have hR : vsz r = vsz (Val.int g) + vsz w + 1 := by rw [hg, auVszCons]
      rw [← auVszInt g]
      exact auSetupCostLe Kd Kuc Kiz Kdr Kps Kcs (vsz (Val.int g)) (vsz w) (vsz r)
        (max c1 c1) hR (le_of_eq (max_self c1))

end Work.Resample
