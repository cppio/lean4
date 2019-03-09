/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.uint init.platform init.data.fin

def usize_sz : nat := (2:nat) ^ system.platform.nbits
structure usize :=
(val : fin usize_sz)

@[extern cpp "lean::usize_of_nat"]
def usize.of_nat (n : @& nat) : usize := ⟨fin.of_nat n⟩
@[extern cpp "lean::usize_to_nat"]
def usize.to_nat (n : usize) : nat := n.val.val
@[extern cpp inline "#1 + #2"]
def usize.add (a b : usize) : usize := ⟨a.val + b.val⟩
@[extern cpp inline "#1 - #2"]
def usize.sub (a b : usize) : usize := ⟨a.val - b.val⟩
@[extern cpp inline "#1 * #2"]
def usize.mul (a b : usize) : usize := ⟨a.val * b.val⟩
@[extern cpp inline "#2 == 0 ? 0 : #1 / #2"]
def usize.div (a b : usize) : usize := ⟨a.val / b.val⟩
@[extern cpp inline "#2 == 0 ? 0 : #1 % #2"]
def usize.mod (a b : usize) : usize := ⟨a.val % b.val⟩
@[extern cpp "lean::usize_modn"]
def usize.modn (a : usize) (n : @& nat) : usize := ⟨a.val %ₙ n⟩
@[extern cpp inline "#1 & #2"]
def usize.land (a b : usize) : usize := ⟨fin.land a.val b.val⟩
@[extern cpp inline "#1 | #2"]
def usize.lor (a b : usize) : usize := ⟨fin.lor a.val b.val⟩
@[extern cpp inline "#1"]
def usize.of_uint32 (a : uint32) : usize := usize.of_nat (uint32.to_nat a)
@[extern cpp inline "((lean::usize)#1)"]
def usize.of_uint64 (a : uint64) : usize := usize.of_nat (uint64.to_nat a)
def usize.lt (a b : usize) : Prop := a.val < b.val
def usize.le (a b : usize) : Prop := a.val ≤ b.val

instance : has_zero usize     := ⟨usize.of_nat 0⟩
instance : has_one usize      := ⟨usize.of_nat 1⟩
instance : has_add usize      := ⟨usize.add⟩
instance : has_sub usize      := ⟨usize.sub⟩
instance : has_mul usize      := ⟨usize.mul⟩
instance : has_mod usize      := ⟨usize.mod⟩
instance : has_modn usize     := ⟨usize.modn⟩
instance : has_div usize      := ⟨usize.div⟩
instance : has_lt usize       := ⟨usize.lt⟩
instance : has_le usize       := ⟨usize.le⟩
instance : inhabited usize    := ⟨0⟩

@[extern cpp inline "#1 == #2"]
def usize.dec_eq (a b : usize) : decidable (a = b) :=
usize.cases_on a $ λ n, usize.cases_on b $ λ m,
  if h : n = m then is_true (h ▸ rfl) else is_false (λ h', usize.no_confusion h' (λ h', absurd h' h))

@[extern cpp inline "#1 < #2"]
def usize.dec_lt (a b : usize) : decidable (a < b) :=
usize.cases_on a $ λ n, usize.cases_on b $ λ m,
  infer_instance_as (decidable (n < m))

@[extern cpp inline "#1 <= #2"]
def usize.dec_le (a b : usize) : decidable (a ≤ b) :=
usize.cases_on a $ λ n, usize.cases_on b $ λ m,
  infer_instance_as (decidable (n <= m))

instance : decidable_eq usize := {dec_eq := usize.dec_eq}
instance usize.has_decidable_lt (a b : usize) : decidable (a < b) := usize.dec_lt a b
instance usize.has_decidable_le (a b : usize) : decidable (a ≤ b) := usize.dec_le a b

theorem usize.modn_lt {m : nat} : ∀ (u : usize), m > 0 → usize.to_nat (u %ₙ m) < m
| ⟨u⟩ h := fin.modn_lt u h
