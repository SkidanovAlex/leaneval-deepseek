import Mathlib
import Submission.Work.Pi6.MSS.AssembleCore
import Submission.Work.Pi6.MSS.pdMulAssoc
import Submission.Work.Pi6.MSS.mssMulLeib
import Submission.Work.Pi6.MSS.mssMulCompat
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# Associativity of the product `mssMul` on the pages of the multiplicative Serre spectral sequence

`mssMul` is the product on the bidegree-indexed pages `mssE 𝕜 W r (s,q) = pEraw 𝕜 W r s (s+q)`
built in `Submission/Work/Pi6/MSS/AssembleCore.lean` by transporting the concrete page product
`pd_mul` along the index equalities `EI (a+b) = EI a + EI b`, `EN (a+b) = EN a + EN b`
(`mssMul_apply_pos`, `Submission/Work/Pi6/MSS/mssMulCompat.lean`).  Since the underlying
Alexander–Whitney product is associative (`pd_mul_assoc_gen`,
`Submission/Work/Pi6/MSS/pdMulAssoc.lean`), the assembled product is associative as well; this
file transfers that associativity through the transports.

The two bookkeeping lemmas `pd_mul_pCast_left`/`pd_mul_pCast_right` record the (evident)
naturality of `pd_mul` with respect to a single `pCast`, in the direction in which it is needed
here: moving a transport of one of the two arguments back out of the product.  The transports
`pCast` depend on their index equalities only through the endpoints (`pCast_congr`), which is
what identifies the two sides at the end.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits

noncomputable section

variable {𝕜 : Type} [Field 𝕜] {W : CohFilt 𝕜}

/-! ## Naturality of `pd_mul` with respect to a transport of one argument -/

theorem pd_mul_pCast_left {r sa na sa' na' sb nb : ℕ}
    (h1 : sa = sa') (h2 : na = na')
    (x : pEraw 𝕜 W r sa na) (y : pEraw 𝕜 W r sb nb) :
    pd_mul r sa' na' sb nb (pCast 𝕜 W r h1 h2 x) y
      = pCast 𝕜 W r (congrArg (· + sb) h1) (congrArg (· + nb) h2)
          (pd_mul r sa na sb nb x y) := by
  cases h1; cases h2
  simp [pCast_apply_self]

theorem pd_mul_pCast_right {r sa na sb nb sb' nb' : ℕ}
    (h1 : sb = sb') (h2 : nb = nb')
    (x : pEraw 𝕜 W r sa na) (y : pEraw 𝕜 W r sb nb) :
    pd_mul r sa na sb' nb' x (pCast 𝕜 W r h1 h2 y)
      = pCast 𝕜 W r (congrArg (sa + ·) h1) (congrArg (na + ·) h2)
          (pd_mul r sa na sb nb x y) := by
  cases h1; cases h2
  simp [pCast_apply_self]

/-- `pCast` depends on its two index equalities only through their endpoints. -/
theorem pCast_congr_apply {r s s' n n' : ℕ}
    (h1 h2 : s = s') (h1' h2' : n = n') (x : pEraw 𝕜 W r s n) :
    pCast 𝕜 W r h1 h1' x = pCast 𝕜 W r h2 h2' x := by
  rw [pCast_congr 𝕜 W r h1 h2 h1' h2']

/-! ## Associativity -/

/-- **Associativity of the product on the pages**, for the transferred product `mssMul`, from the
associativity of the underlying product on the filtered complex. -/
theorem mssMulAssoc_gen
    (hassoc : ∀ (n m k : ℕ) (x : W.C.X n) (y : W.C.X m) (z : W.C.X k),
      W.xcast (Nat.add_assoc n m k) (W.mul (n+m) k (W.mul n m x y) z)
        = W.mul n (m+k) x (W.mul m k y z))
    (r : ℕ) (a b c ab bc d : ℤ × ℤ) (ha : Enn a) (hb : Enn b) (hc : Enn c)
    (hab : a + b = ab) (hbc : b + c = bc) (h1 : ab + c = d) (h2 : a + bc = d)
    (x : mssE 𝕜 W r a) (y : mssE 𝕜 W r b) (z : mssE 𝕜 W r c) :
    mssMul 𝕜 W r ab c d h1 (mssMul 𝕜 W r a b ab hab x y) z
      = mssMul 𝕜 W r a bc d h2 x (mssMul 𝕜 W r b c bc hbc y z) := by
  have hab' : Enn ab := hab ▸ Enn_add ha hb
  have hbc' : Enn bc := hbc ▸ Enn_add hb hc
  -- the index equalities attached to the two triple products
  have hA : EI a + EI b = EI ab := (EI_add ha hb).trans (congrArg EI hab)
  have hN : EN a + EN b = EN ab := (EN_add ha hb).trans (congrArg EN hab)
  have hB : EI b + EI c = EI bc := (EI_add hb hc).trans (congrArg EI hbc)
  have hM : EN b + EN c = EN bc := (EN_add hb hc).trans (congrArg EN hbc)
  have hE : (EI a + EI b) + EI c = EI a + (EI b + EI c) := by omega
  have hE' : (EN a + EN b) + EN c = EN a + (EN b + EN c) := by omega
  -- the associativity of the underlying product `pd_mul`
  have hZ2 : pd_mul r (EI a) (EN a) (EI b + EI c) (EN b + EN c) x
        (pd_mul r (EI b) (EN b) (EI c) (EN c) y z)
      = pCast 𝕜 W r hE hE'
          (pd_mul r (EI a + EI b) (EN a + EN b) (EI c) (EN c)
            (pd_mul r (EI a) (EN a) (EI b) (EN b) x y) z) := by
    rw [← pd_mul_assoc_gen hassoc r (EI a) (EN a) (EI b) (EN b) (EI c) (EN c) x y z]
    rw [pEcast_hom_apply]
  -- rewrite both sides in terms of `pd_mul` on the `EI`/`EN` indices
  rw [mssMul_apply_pos (𝕜 := 𝕜) (W := W) (r := r) (a := ab) (b := c) (c := d)
        (ha := hab') (hb := hc) (h := h1)]
  rw [mssMul_apply_pos (𝕜 := 𝕜) (W := W) (r := r) (a := a) (b := b) (c := ab)
        (ha := ha) (hb := hb) (h := hab)]
  rw [mssMul_apply_pos (𝕜 := 𝕜) (W := W) (r := r) (a := a) (b := bc) (c := d)
        (ha := ha) (hb := hbc') (h := h2)]
  rw [mssMul_apply_pos (𝕜 := 𝕜) (W := W) (r := r) (a := b) (b := c) (c := bc)
        (ha := hb) (hb := hc) (h := hbc)]
  -- merge the nested transports
  repeat rw [pCast_comp_apply]
  -- move the transport of the first argument out of the left hand product
  rw [pd_mul_pCast_left hA hN _ z]
  repeat rw [pCast_comp_apply]
  -- move the transport of the second argument out of the right hand product
  rw [pd_mul_pCast_right hB hM x _]
  -- and use the associativity of `pd_mul`
  rw [hZ2]
  -- both sides are now transports of the same element along equalities with the same endpoints
  repeat rw [pCast_comp_apply]

end

/-- **Associativity of the product** on the pages of the multiplicative cohomological Serre
spectral sequence: the product used in the computation of `π₆(S³)`. -/
theorem mssMulAssoc (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (r : ℕ)
    (a b c ab bc d : ℤ × ℤ) (ha : Work.Pi6.MSS.Enn a) (hb : Work.Pi6.MSS.Enn b)
    (hc : Work.Pi6.MSS.Enn c)
    (hab : a + b = ab) (hbc : b + c = bc) (h1 : ab + c = d) (h2 : a + bc = d)
    (x : Work.Pi6.MSS.mssE 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) r a)
    (y : Work.Pi6.MSS.mssE 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) r b)
    (z : Work.Pi6.MSS.mssE 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) r c) :
    Work.Pi6.MSS.mssMul 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) r ab c d h1
        (Work.Pi6.MSS.mssMul 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) r a b ab hab x y) z
      = Work.Pi6.MSS.mssMul 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) r a bc d h2 x
          (Work.Pi6.MSS.mssMul 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) r b c bc hbc y z) :=
  mssMulAssoc_gen (𝕜 := 𝕜) (W := serreCF 𝕜 E B p) (serreCF_xcast_mul 𝕜 E B p)
    r a b c ab bc d ha hb hc hab hbc h1 h2 x y z

end Work.Pi6.MSS
