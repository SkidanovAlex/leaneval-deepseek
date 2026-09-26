import Mathlib
import Submission.Work.Smooth.JordanSeparation.lwalk_cornerglue
import Submission.Work.Smooth.JordanSeparation.lwalk_transport

/-!
# Interface lemmas for the corner move of the peel

`joinNat_of_eq` moves a `joinNat` across a rewriting of its index, and `edgeUNat_apply_of` compares
the values of the clamped lifted edges of two walks whose vertices agree at two consecutive indices.
These are the two value-level tools the corner step of the peel (`W.loopNat ~ (W.flip …).loopNat`)
needs when the flipped walk drops one index.
-/

namespace Work.Smooth.JordanSeparation

open Set Metric

noncomputable section

/-- A `joinNat` is a cast of the `joinNat` at a (propositionally) equal index. -/
theorem joinNat_of_eq {X : Type*} [TopologicalSpace X] {p : ℕ → X} (F : ∀ k, Path (p k) (p (k + 1)))
    {m n : ℕ} (h : m = n) : joinNat F m = Path.cast (joinNat F n) rfl (congrArg p h) := by
  subst h
  rw [Path.cast_self]

/-- The values of the clamped lifted edges of two walks whose vertices agree at the two endpoints of
the edge. -/
theorem edgeUNat_apply_of {U : Set ℂ} {X X' : LWalk} {hX : ∀ t, X.path t ∈ U}
    {hX' : ∀ t, X'.path t ∈ U} {m : ℕ} (hm : m < X.n) (hm' : m < X'.n) (hc : X'.c = X.c)
    (hpt : X'.v m = X.v m) (hpt' : X'.v (m + 1) = X.v (m + 1)) (t : unitInterval) :
    ((X'.edgeUNat hX' m t : ↥U) : ℂ) = ((X.edgeUNat hX m t : ↥U) : ℂ) := by
  have h1 : X'.pt m = X.pt m := by show X'.c * gpt (X'.v m) = X.c * gpt (X.v m); rw [hc, hpt]
  have h2 : X'.pt (m + 1) = X.pt (m + 1) := by
    show X'.c * gpt (X'.v (m + 1)) = X.c * gpt (X.v (m + 1)); rw [hc, hpt']
  rw [LWalk.edgeUNat_apply, LWalk.edgeUNat_apply, dif_pos hm', dif_pos hm]
  simp only [LWalk.edge, segPath]
  rw [Path.segment_apply, Path.segment_apply, h1, h2]

/-- The clamped lifted edge of `X'` is the one of `X`, transported along the endpoint
equalities. -/
theorem edgeUNat_eq_cast_of {U : Set ℂ} {X X' : LWalk} {hX : ∀ t, X.path t ∈ U}
    {hX' : ∀ t, X'.path t ∈ U} {m : ℕ} (hm : m < X.n) (hm' : m < X'.n) (hc : X'.c = X.c)
    (hpt : X'.v m = X.v m) (hpt' : X'.v (m + 1) = X.v (m + 1))
    (e : X'.ptMin hX' m = X.ptMin hX m) (e' : X'.ptMin hX' (m + 1) = X.ptMin hX (m + 1)) :
    Path.cast (X.edgeUNat hX m) e e' = X'.edgeUNat hX' m := by
  apply Path.ext
  funext t
  rw [path_cast_apply]
  exact Subtype.ext (by rw [← edgeUNat_apply_of hm hm' hc hpt hpt' t])

/-! ### The flipped walk against the original, away from the corner -/

/-- The vertices of the flipped walk agree with those of the original away from the flipped
index. -/
theorem flip_ptMin_eq {U : Set ℂ} {W : LWalk} {hval : ∀ t, W.path t ∈ U} {k : ℕ}
    (hk1 : 1 ≤ k) (hk2 : k + 1 ≤ W.n)
    (ha : W.v (k - 1) = W.v k - (1, 0) ∨ W.v (k - 1) = W.v k - (0, 1))
    (hb : W.v (k + 1) = W.v k - (1, 0) ∨ W.v (k + 1) = W.v k - (0, 1))
    (hval' : ∀ t, (W.flip hk1 hk2 ha hb).path t ∈ U) {j : ℕ} (hj : j ≤ W.n) (hj0 : j ≠ k) :
    W.ptMin hval j = (W.flip hk1 hk2 ha hb).ptMin hval' j := by
  refine Subtype.ext ?_
  show W.pt (min j W.n) = (W.flip hk1 hk2 ha hb).pt (min j W.n)
  rw [Nat.min_eq_left hj]
  show W.c * gpt (W.v j) = (W.flip hk1 hk2 ha hb).c * gpt ((W.flip hk1 hk2 ha hb).v j)
  rw [LWalk.flip_c, LWalk.flip_v_of_ne W hk1 hk2 ha hb hj0]

/-- The clamped lifted edges of the flipped walk agree with those of the original away from the
corner. -/
theorem flip_edgeUNat_eq {U : Set ℂ} {W : LWalk} {hval : ∀ t, W.path t ∈ U} {k : ℕ}
    (hk1 : 1 ≤ k) (hk2 : k + 1 ≤ W.n)
    (ha : W.v (k - 1) = W.v k - (1, 0) ∨ W.v (k - 1) = W.v k - (0, 1))
    (hb : W.v (k + 1) = W.v k - (1, 0) ∨ W.v (k + 1) = W.v k - (0, 1))
    (hval' : ∀ t, (W.flip hk1 hk2 ha hb).path t ∈ U) {m : ℕ} (hm : m < W.n)
    (hmk : m ≠ k) (hmk' : m + 1 ≠ k) :
    Path.cast ((W.flip hk1 hk2 ha hb).edgeUNat hval' m)
        (flip_ptMin_eq hk1 hk2 ha hb hval' (le_of_lt hm) hmk)
        (flip_ptMin_eq hk1 hk2 ha hb hval' (by omega) hmk')
      = W.edgeUNat hval m := by
  have h := edgeUNat_eq_cast_of (X := W) (X' := W.flip hk1 hk2 ha hb) (hX := hval)
    (hX' := hval') hm (by rwa [LWalk.flip_n]) (LWalk.flip_c W hk1 hk2 ha hb)
    (LWalk.flip_v_of_ne W hk1 hk2 ha hb hmk) (LWalk.flip_v_of_ne W hk1 hk2 ha hb hmk')
    (flip_ptMin_eq hk1 hk2 ha hb hval' (le_of_lt hm) hmk).symm
    (flip_ptMin_eq hk1 hk2 ha hb hval' (by omega) hmk').symm
  rw [← h]
  rw [Path.cast_cast, Path.cast_self]

/-- The reversed form of `flip_edgeUNat_eq`, in the shape `joinNat_cast` wants. -/
theorem flip_edgeUNat_eq' {U : Set ℂ} {W : LWalk} {hval : ∀ t, W.path t ∈ U} {k : ℕ}
    (hk1 : 1 ≤ k) (hk2 : k + 1 ≤ W.n)
    (ha : W.v (k - 1) = W.v k - (1, 0) ∨ W.v (k - 1) = W.v k - (0, 1))
    (hb : W.v (k + 1) = W.v k - (1, 0) ∨ W.v (k + 1) = W.v k - (0, 1))
    (hval' : ∀ t, (W.flip hk1 hk2 ha hb).path t ∈ U) {m : ℕ} (hm : m < W.n)
    (hmk : m ≠ k) (hmk' : m + 1 ≠ k) :
    (W.flip hk1 hk2 ha hb).edgeUNat hval' m
      = Path.cast (W.edgeUNat hval m)
          (flip_ptMin_eq hk1 hk2 ha hb hval' (le_of_lt hm) hmk).symm
          (flip_ptMin_eq hk1 hk2 ha hb hval' (by omega) hmk').symm := by
  rw [← flip_edgeUNat_eq hk1 hk2 ha hb hval' hm hmk hmk', Path.cast_cast, Path.cast_self]

/-- Two `Path.cast`s of the same path along possibly different proofs of the same endpoint
equalities are equal (the endpoint arguments are proofs of propositions). -/
theorem path_cast_proof_irrel {X : Type*} [TopologicalSpace X] {x y x' y' : X} (γ : Path x y)
    (hx hx' : x' = x) (hy hy' : y' = y) : Path.cast γ hx hy = Path.cast γ hx' hy' := by
  apply Path.ext
  funext t
  rw [path_cast_apply]

end

end Work.Smooth.JordanSeparation
